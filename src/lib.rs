//! nom_locate, a special input type to locate tokens
//!
//! The source code is available on [Github](https://github.com/fflorent/nom_locate)
//!
//! ## Features
//!
//! This crate exposes two cargo feature flags, `generic-simd` and `runtime-dispatch-simd`.
//! These correspond to the features exposed by [bytecount](https://github.com/llogiq/bytecount).
//!
//! ## How to use it
//! The explanations are given in the [README](https://github.com/fflorent/nom_locate/blob/master/README.md) of the Github repository. You may also consult the [FAQ](https://github.com/fflorent/nom_locate/blob/master/FAQ.md).
//!
//! ```
//! use nom::bytes::complete::{tag, take_until};
//! use nom::IResult;
//! use nom_locate::{position, LocatedSpan};
//!
//! type Span<'a> = LocatedSpan<&'a str>;
//!
//! struct Token<'a> {
//!     pub position: Span<'a>,
//!     pub foo: &'a str,
//!     pub bar: &'a str,
//! }
//!
//! fn parse_foobar(s: Span) -> IResult<Span, Token> {
//!     let (s, _) = take_until("foo")(s)?;
//!     let (s, pos) = position(s)?;
//!     let (s, foo) = tag("foo")(s)?;
//!     let (s, bar) = tag("bar")(s)?;
//!
//!     Ok((
//!         s,
//!         Token {
//!             position: pos,
//!             foo: foo.fragment(),
//!             bar: bar.fragment(),
//!         },
//!     ))
//! }
//!
//! fn main () {
//!     let input = Span::new("Lorem ipsum \n foobar");
//!     let output = parse_foobar(input);
//!     let position = output.unwrap().1.position;
//!     assert_eq!(position.location_offset(), 14);
//!     assert_eq!(position.location_line(), 2);
//!     assert_eq!(position.fragment(), &"");
//!     assert_eq!(position.get_column(), 2);
//! }
//! ```
//!
//! ## Extra information
//!
//! You can also add arbitrary extra information using the extra property of `LocatedSpan`.
//! This property is not used when comparing two `LocatedSpan`s.
//!
//! ```ignore
//! use nom_locate::LocatedSpan;
//! type Span<'a> = LocatedSpan<&'a str, String>;
//!
//! let input = Span::new_extra("Lorem ipsum \n foobar", "filename");
//! let output = parse_foobar(input);
//! let extra = output.unwrap().1.extra;
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(all(not(feature = "std"), feature = "alloc"))]
#[cfg_attr(test, macro_use)]
extern crate alloc;

#[cfg(test)]
mod tests;

mod lib {
    #[cfg(feature = "std")]
    pub mod std {
        pub use std::fmt::{Display, Formatter, Result as FmtResult};
        pub use std::hash::{Hash, Hasher};
        pub use std::iter::{Copied, Enumerate};
        pub use std::ops::{Range, RangeFrom, RangeFull, RangeTo};
        pub use std::slice;
        pub use std::slice::Iter;
        pub use std::str::{CharIndices, Chars, FromStr};
        pub use std::string::{String, ToString};
        pub use std::vec::Vec;
    }

    #[cfg(not(feature = "std"))]
    pub mod std {
        #[cfg(feature = "alloc")]
        pub use alloc::fmt::{Display, Formatter, Result as FmtResult};
        #[cfg(feature = "alloc")]
        pub use alloc::string::{String, ToString};
        #[cfg(feature = "alloc")]
        pub use alloc::vec::Vec;
        pub use core::hash::{Hash, Hasher};
        pub use core::iter::{Copied, Enumerate};
        pub use core::ops::{Range, RangeFrom, RangeFull, RangeTo};
        pub use core::slice;
        pub use core::slice::Iter;
        pub use core::str::{CharIndices, Chars, FromStr};
    }
}

use lib::std::*;

use bytecount::{naive_num_chars, num_chars};
use memchr::Memchr;
#[cfg(feature = "alloc")]
use nom::ExtendInto;
use nom::{
    error::{ErrorKind, ParseError},
    AsBytes, Compare, CompareResult, Err, FindSubstring, FindToken, IResult, InputIter,
    InputLength, InputTake, InputTakeAtPosition, Offset, ParseTo, Slice,
};
#[cfg(feature = "stable-deref-trait")]
use stable_deref_trait::StableDeref;

/// A LocatedSpan is a set of meta information about the location of a token, including extra
/// information.
///
/// The `LocatedSpan` structure can be used as an input of the nom parsers.
/// It implements all the necessary traits for `LocatedSpan<&str,X>` and `LocatedSpan<&[u8],X>`
#[derive(Debug, Clone, Copy)]
pub struct LocatedSpan<T, X = ()> {
    /// The offset represents the position of the fragment relatively to
    /// the input of the parser. It starts at offset 0.
    offset: usize,

    /// The line number of the fragment relatively to the input of the
    /// parser. It starts at line 1.
    line: u32,

    /// The fragment that is spanned.
    /// The fragment represents a part of the input of the parser.
    fragment: T,

    /// Extra information that can be embedded by the user.
    /// Example: the parsed file name
    pub extra: X,
}

impl<T, X> core::ops::Deref for LocatedSpan<T, X> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.fragment
    }
}

impl<T, U, X> core::convert::AsRef<U> for LocatedSpan<&T, X>
where
    T: ?Sized + core::convert::AsRef<U>,
    U: ?Sized,
{
    fn as_ref(&self) -> &U {
        self.fragment.as_ref()
    }
}

#[cfg(feature = "stable-deref-trait")]
/// Optionally impl StableDeref so that this type works harmoniously with other
/// crates that rely on this marker trait, such as `rental` and `lazy_static`.
/// LocatedSpan is largely just a wrapper around the contained type `T`, so
/// this marker trait is safe to implement whenever T already implements
/// StableDeref.
unsafe impl<T: StableDeref, X> StableDeref for LocatedSpan<T, X> {}

impl<T> LocatedSpan<T, ()> {
    /// Create a span for a particular input with default `offset` and
    /// `line` values and empty extra data.
    /// You can compute the column through the `get_column` or `get_utf8_column`
    /// methods.
    ///
    /// `offset` starts at 0, `line` starts at 1, and `column` starts at 1.
    ///
    /// Do not use this constructor in parser functions; `nom` and
    /// `nom_locate` assume span offsets are relative to the beginning of the
    /// same input. In these cases, you probably want to use the
    /// `nom::traits::Slice` trait instead.
    ///
    /// # Example of use
    ///
    /// ```
    /// # extern crate nom_locate;
    /// use nom_locate::LocatedSpan;
    ///
    /// # fn main() {
    /// let span = LocatedSpan::new(b"foobar");
    ///
    /// assert_eq!(span.location_offset(), 0);
    /// assert_eq!(span.location_line(),   1);
    /// assert_eq!(span.get_column(),      1);
    /// assert_eq!(span.fragment(),        &&b"foobar"[..]);
    /// # }
    /// ```
    pub fn new(program: T) -> LocatedSpan<T, ()> {
        LocatedSpan {
            offset: 0,
            line: 1,
            fragment: program,
            extra: (),
        }
    }
}

impl<T, X> LocatedSpan<T, X> {
    /// Create a span for a particular input with default `offset` and
    /// `line` values. You can compute the column through the `get_column` or `get_utf8_column`
    /// methods.
    ///
    /// `offset` starts at 0, `line` starts at 1, and `column` starts at 1.
    ///
    /// Do not use this constructor in parser functions; `nom` and
    /// `nom_locate` assume span offsets are relative to the beginning of the
    /// same input. In these cases, you probably want to use the
    /// `nom::traits::Slice` trait instead.
    ///
    /// # Example of use
    ///
    /// ```
    /// # extern crate nom_locate;
    /// use nom_locate::LocatedSpan;
    ///
    /// # fn main() {
    /// let span = LocatedSpan::new_extra(b"foobar", "extra");
    ///
    /// assert_eq!(span.location_offset(), 0);
    /// assert_eq!(span.location_line(),   1);
    /// assert_eq!(span.get_column(),      1);
    /// assert_eq!(span.fragment(),        &&b"foobar"[..]);
    /// assert_eq!(span.extra,             "extra");
    /// # }
    /// ```
    pub fn new_extra(program: T, extra: X) -> LocatedSpan<T, X> {
        LocatedSpan {
            offset: 0,
            line: 1,
            fragment: program,
            extra: extra,
        }
    }

    /// Similar to `new_extra`, but allows overriding offset and line.
    /// This is unsafe, because giving an offset too large may result in
    /// undefined behavior, as some methods move back along the fragment
    /// assuming any negative index within the offset is valid.
    pub unsafe fn new_from_raw_offset(
        offset: usize,
        line: u32,
        fragment: T,
        extra: X,
    ) -> LocatedSpan<T, X> {
        LocatedSpan {
            offset,
            line,
            fragment,
            extra,
        }
    }

    /// The offset represents the position of the fragment relatively to
    /// the input of the parser. It starts at offset 0.
    pub fn location_offset(&self) -> usize {
        self.offset
    }

    /// The line number of the fragment relatively to the input of the
    /// parser. It starts at line 1.
    pub fn location_line(&self) -> u32 {
        self.line
    }

    /// The fragment that is spanned.
    /// The fragment represents a part of the input of the parser.
    pub fn fragment(&self) -> &T {
        &self.fragment
    }

    /// Transform the extra inside into another type
    ///
    /// # Example of use
    /// ```
    /// # extern crate nom_locate;
    /// # extern crate nom;
    /// # use nom_locate::LocatedSpan;
    /// use nom::{
    ///   IResult,
    ///   combinator::{recognize, map_res},
    ///   sequence::{terminated, tuple},
    ///   character::{complete::{char, one_of}, is_digit},
    ///   bytes::complete::{tag, take_while1}
    /// };
    ///
    /// fn decimal(input: LocatedSpan<&str>) -> IResult<LocatedSpan<&str>, LocatedSpan<&str>> {
    ///   recognize(
    ///        take_while1(|c| is_digit(c as u8) || c == '_')
    ///   )(input)
    /// }
    ///
    /// fn main() {
    ///     let span = LocatedSpan::new("$10");
    ///     // matches the $ and then matches the decimal number afterwards,
    ///     // converting it into a `u8` and putting that value in the span
    ///     let (_, (_, n)) = tuple((
    ///                         tag("$"),
    ///                         map_res(
    ///                             decimal,
    ///                             |x| x.fragment().parse::<u8>().map(|n| x.map_extra(|_| n))
    ///                         )
    ///                       ))(span).unwrap();
    ///     assert_eq!(n.extra, 10);
    /// }
    /// ```
    pub fn map_extra<U, F: FnOnce(X) -> U>(self, f: F) -> LocatedSpan<T, U> {
        LocatedSpan {
            offset: self.offset,
            line: self.line,
            fragment: self.fragment,
            extra: f(self.extra),
        }
    }

    /// Takes ownership of the fragment without (re)borrowing it.
    ///
    /// # Example of use
    /// ```
    /// # extern crate nom_locate;
    /// # extern crate nom;
    /// # use nom_locate::LocatedSpan;
    /// use nom::{
    ///     IResult,
    ///     bytes::complete::{take_till, tag},
    ///     combinator::rest,
    /// };
    ///
    /// fn parse_pair<'a>(input: LocatedSpan<&'a str>) -> IResult<LocatedSpan<&'a str>, (&'a str, &'a str)> {
    ///     let (input, key) = take_till(|c| c == '=')(input)?;
    ///     let (input, _) = tag("=")(input)?;
    ///     let (input, value) = rest(input)?;
    ///
    ///     Ok((input, (key.into_fragment(), value.into_fragment())))
    /// }
    ///
    /// fn main() {
    ///     let span = LocatedSpan::new("key=value");
    ///     let (_, pair) = parse_pair(span).unwrap();
    ///     assert_eq!(pair, ("key", "value"));
    /// }
    /// ```
    pub fn into_fragment(self) -> T {
        self.fragment
    }

    /// Takes ownership of the fragment and extra data without (re)borrowing them.
    pub fn into_fragment_and_extra(self) -> (T, X) {
        (self.fragment, self.extra)
    }
}

impl<T: AsBytes, X> LocatedSpan<T, X> {
    // Attempt to get the "original" data slice back, by extending
    // self.fragment backwards by self.offset.
    // Note that any bytes truncated from after self.fragment will not
    // be recovered.
    fn get_unoffsetted_slice(&self) -> &[u8] {
        let self_bytes = self.fragment.as_bytes();
        let self_ptr = self_bytes.as_ptr();
        unsafe {
            assert!(
                self.offset <= isize::max_value() as usize,
                "offset is too big"
            );
            let orig_input_ptr = self_ptr.offset(-(self.offset as isize));
            slice::from_raw_parts(orig_input_ptr, self.offset + self_bytes.len())
        }
    }

    fn get_columns_and_bytes_before(&self) -> (usize, &[u8]) {
        let before_self = &self.get_unoffsetted_slice()[..self.offset];

        let column = match memchr::memrchr(b'\n', before_self) {
            None => self.offset + 1,
            Some(pos) => self.offset - pos,
        };

        (column, &before_self[self.offset - (column - 1)..])
    }

    /// Return the line that contains this LocatedSpan.
    ///
    /// The `get_column` and `get_utf8_column` functions returns
    /// indexes that corresponds to the line returned by this function.
    ///
    /// Note that if this LocatedSpan ends before the end of the
    /// original data, the result of calling `get_line_beginning()`
    /// will not include any data from after the LocatedSpan.
    ///
    /// ```
    /// # extern crate nom_locate;
    /// # extern crate nom;
    /// # use nom_locate::LocatedSpan;
    /// # use nom::{Slice, FindSubstring};
    /// #
    /// # fn main() {
    /// let program = LocatedSpan::new(
    ///     "Hello World!\
    ///     \nThis is a multi-line input\
    ///     \nthat ends after this line.\n");
    /// let multi = program.find_substring("multi").unwrap();
    ///
    /// assert_eq!(
    ///     program.slice(multi..).get_line_beginning(),
    ///     "This is a multi-line input".as_bytes(),
    /// );
    /// # }
    /// ```
    pub fn get_line_beginning(&self) -> &[u8] {
        let column0 = self.get_column() - 1;
        let the_line = &self.get_unoffsetted_slice()[self.offset - column0..];
        match memchr::memchr(b'\n', &the_line[column0..]) {
            None => the_line,
            Some(pos) => &the_line[..column0 + pos],
        }
    }

    /// Return the column index, assuming 1 byte = 1 column.
    ///
    /// Use it for ascii text, or use get_utf8_column for UTF8.
    ///
    /// # Example of use
    /// ```
    ///
    /// # extern crate nom_locate;
    /// # extern crate nom;
    /// # use nom_locate::LocatedSpan;
    /// # use nom::Slice;
    /// #
    /// # fn main() {
    /// let span = LocatedSpan::new("foobar");
    ///
    /// assert_eq!(span.slice(3..).get_column(), 4);
    /// # }
    /// ```
    pub fn get_column(&self) -> usize {
        self.get_columns_and_bytes_before().0
    }

    /// Return the column index for UTF8 text. Return value is unspecified for non-utf8 text.
    ///
    /// This version uses bytecount's hyper algorithm to count characters. This is much faster
    /// for long lines, but is non-negligibly slower for short slices (below around 100 bytes).
    /// This is also sped up significantly more depending on architecture and enabling the simd
    /// feature gates. If you expect primarily short lines, you may get a noticeable speedup in
    /// parsing by using `naive_get_utf8_column` instead. Benchmark your specific use case!
    ///
    /// # Example of use
    /// ```
    ///
    /// # extern crate nom_locate;
    /// # extern crate nom;
    /// # use nom_locate::LocatedSpan;
    /// # use nom::{Slice, FindSubstring};
    /// #
    /// # fn main() {
    /// let span = LocatedSpan::new("メカジキ");
    /// let indexOf3dKanji = span.find_substring("ジ").unwrap();
    ///
    /// assert_eq!(span.slice(indexOf3dKanji..).get_column(), 7);
    /// assert_eq!(span.slice(indexOf3dKanji..).get_utf8_column(), 3);
    /// # }
    /// ```
    pub fn get_utf8_column(&self) -> usize {
        let before_self = self.get_columns_and_bytes_before().1;
        num_chars(before_self) + 1
    }

    /// Return the column index for UTF8 text. Return value is unspecified for non-utf8 text.
    ///
    /// A simpler implementation of `get_utf8_column` that may be faster on shorter lines.
    /// If benchmarking shows that this is faster, you can use it instead of `get_utf8_column`.
    /// Prefer defaulting to `get_utf8_column` unless this legitimately is a performance bottleneck.
    ///
    /// # Example of use
    /// ```
    ///
    /// # extern crate nom_locate;
    /// # extern crate nom;
    /// # use nom_locate::LocatedSpan;
    /// # use nom::{Slice, FindSubstring};
    /// #
    /// # fn main() {
    /// let span = LocatedSpan::new("メカジキ");
    /// let indexOf3dKanji = span.find_substring("ジ").unwrap();
    ///
    /// assert_eq!(span.slice(indexOf3dKanji..).get_column(), 7);
    /// assert_eq!(span.slice(indexOf3dKanji..).naive_get_utf8_column(), 3);
    /// # }
    /// ```
    pub fn naive_get_utf8_column(&self) -> usize {
        let before_self = self.get_columns_and_bytes_before().1;
        naive_num_chars(before_self) + 1
    }
}

impl<T: Hash, X> Hash for LocatedSpan<T, X> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.offset.hash(state);
        self.line.hash(state);
        self.fragment.hash(state);
    }
}

impl<T: AsBytes, X: Default> From<T> for LocatedSpan<T, X> {
    fn from(i: T) -> Self {
        Self::new_extra(i, X::default())
    }
}

impl<T: AsBytes + PartialEq, X> PartialEq for LocatedSpan<T, X> {
    fn eq(&self, other: &Self) -> bool {
        self.line == other.line && self.offset == other.offset && self.fragment == other.fragment
    }
}

impl<T: AsBytes + Eq, X> Eq for LocatedSpan<T, X> {}

impl<T: AsBytes, X> AsBytes for LocatedSpan<T, X> {
    fn as_bytes(&self) -> &[u8] {
        self.fragment.as_bytes()
    }
}

impl<T: InputLength, X> InputLength for LocatedSpan<T, X> {
    fn input_len(&self) -> usize {
        self.fragment.input_len()
    }
}

impl<T, X> InputTake for LocatedSpan<T, X>
where
    Self: Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
{
    fn take(&self, count: usize) -> Self {
        self.slice(..count)
    }

    fn take_split(&self, count: usize) -> (Self, Self) {
        (self.slice(count..), self.slice(..count))
    }
}

impl<T, X> InputTakeAtPosition for LocatedSpan<T, X>
where
    T: InputTakeAtPosition + InputLength + InputIter,
    Self: Slice<RangeFrom<usize>> + Slice<RangeTo<usize>> + Clone,
{
    type Item = <T as InputIter>::Item;

    fn split_at_position_complete<P, E: ParseError<Self>>(
        &self,
        predicate: P,
    ) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
    {
        match self.split_at_position(predicate) {
            Err(Err::Incomplete(_)) => Ok(self.take_split(self.input_len())),
            res => res,
        }
    }

    fn split_at_position<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
    {
        match self.fragment.position(predicate) {
            Some(n) => Ok(self.take_split(n)),
            None => Err(Err::Incomplete(nom::Needed::new(1))),
        }
    }

    fn split_at_position1<P, E: ParseError<Self>>(
        &self,
        predicate: P,
        e: ErrorKind,
    ) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
    {
        match self.fragment.position(predicate) {
            Some(0) => Err(Err::Error(E::from_error_kind(self.clone(), e))),
            Some(n) => Ok(self.take_split(n)),
            None => Err(Err::Incomplete(nom::Needed::new(1))),
        }
    }

    fn split_at_position1_complete<P, E: ParseError<Self>>(
        &self,
        predicate: P,
        e: ErrorKind,
    ) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
    {
        match self.fragment.position(predicate) {
            Some(0) => Err(Err::Error(E::from_error_kind(self.clone(), e))),
            Some(n) => Ok(self.take_split(n)),
            None => {
                if self.fragment.input_len() == 0 {
                    Err(Err::Error(E::from_error_kind(self.clone(), e)))
                } else {
                    Ok(self.take_split(self.input_len()))
                }
            }
        }
    }
}

#[macro_export]
#[deprecated(
    since = "3.1.0",
    note = "this implementation has been generalized and no longer requires a macro"
)]
macro_rules! impl_input_iter {
    () => {};
}

impl<'a, T, X> InputIter for LocatedSpan<T, X>
where
    T: InputIter,
{
    type Item = T::Item;
    type Iter = T::Iter;
    type IterElem = T::IterElem;
    #[inline]
    fn iter_indices(&self) -> Self::Iter {
        self.fragment.iter_indices()
    }
    #[inline]
    fn iter_elements(&self) -> Self::IterElem {
        self.fragment.iter_elements()
    }
    #[inline]
    fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        self.fragment.position(predicate)
    }
    #[inline]
    fn slice_index(&self, count: usize) -> Result<usize, nom::Needed> {
        self.fragment.slice_index(count)
    }
}

impl<A: Compare<B>, B: Into<LocatedSpan<B>>, X> Compare<B> for LocatedSpan<A, X> {
    #[inline(always)]
    fn compare(&self, t: B) -> CompareResult {
        self.fragment.compare(t.into().fragment)
    }

    #[inline(always)]
    fn compare_no_case(&self, t: B) -> CompareResult {
        self.fragment.compare_no_case(t.into().fragment)
    }
}

#[macro_export]
#[deprecated(
    since = "2.1.0",
    note = "this implementation has been generalized and no longer requires a macro"
)]
macro_rules! impl_compare {
    ( $fragment_type:ty, $compare_to_type:ty ) => {};
}

#[macro_export]
#[deprecated(
    since = "3.1.0",
    note = "this implementation has been generalized and no longer requires a macro"
)]
macro_rules! impl_slice_range {
    ( $fragment_type:ty, $range_type:ty, $can_return_self:expr ) => {};
}

#[macro_export]
#[deprecated(
    since = "3.1.0",
    note = "this implementation has been generalized and no longer requires a macro"
)]
macro_rules! impl_slice_ranges {
    ( $fragment_type:ty ) => {};
}

impl<'a, T, R, X: Clone> Slice<R> for LocatedSpan<T, X>
where
    T: Slice<R> + Offset + AsBytes + Slice<RangeTo<usize>>,
{
    fn slice(&self, range: R) -> Self {
        let next_fragment = self.fragment.slice(range);
        let consumed_len = self.fragment.offset(&next_fragment);
        if consumed_len == 0 {
            return LocatedSpan {
                line: self.line,
                offset: self.offset,
                fragment: next_fragment,
                extra: self.extra.clone(),
            };
        }

        let consumed = self.fragment.slice(..consumed_len);

        let next_offset = self.offset + consumed_len;

        let consumed_as_bytes = consumed.as_bytes();
        let iter = Memchr::new(b'\n', consumed_as_bytes);
        let number_of_lines = iter.count() as u32;
        let next_line = self.line + number_of_lines;

        LocatedSpan {
            line: next_line,
            offset: next_offset,
            fragment: next_fragment,
            extra: self.extra.clone(),
        }
    }
}

impl<Fragment: FindToken<Token>, Token, X> FindToken<Token> for LocatedSpan<Fragment, X> {
    fn find_token(&self, token: Token) -> bool {
        self.fragment.find_token(token)
    }
}

impl<T, U, X> FindSubstring<U> for LocatedSpan<T, X>
where
    T: FindSubstring<U>,
{
    #[inline]
    fn find_substring(&self, substr: U) -> Option<usize> {
        self.fragment.find_substring(substr)
    }
}

impl<R: FromStr, T, X> ParseTo<R> for LocatedSpan<T, X>
where
    T: ParseTo<R>,
{
    #[inline]
    fn parse_to(&self) -> Option<R> {
        self.fragment.parse_to()
    }
}

impl<T, X> Offset for LocatedSpan<T, X> {
    fn offset(&self, second: &Self) -> usize {
        let fst = self.offset;
        let snd = second.offset;

        snd - fst
    }
}

#[cfg(feature = "alloc")]
impl<T: ToString, X> Display for LocatedSpan<T, X> {
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult {
        fmt.write_str(&self.fragment.to_string())
    }
}

#[macro_export]
#[deprecated(
    since = "3.1.0",
    note = "this implementation has been generalized and no longer requires a macro"
)]
macro_rules! impl_extend_into {
    ($fragment_type:ty, $item:ty, $extender:ty) => {
        impl<'a, X> ExtendInto for LocatedSpan<$fragment_type, X> {
            type Item = $item;
            type Extender = $extender;

            #[inline]
            fn new_builder(&self) -> Self::Extender {
                self.fragment.new_builder()
            }

            #[inline]
            fn extend_into(&self, acc: &mut Self::Extender) {
                self.fragment.extend_into(acc)
            }
        }
    };
}

#[cfg(feature = "alloc")]
impl<'a, T, X> ExtendInto for LocatedSpan<T, X>
where
    T: ExtendInto,
{
    type Item = T::Item;
    type Extender = T::Extender;

    #[inline]
    fn new_builder(&self) -> Self::Extender {
        self.fragment.new_builder()
    }

    #[inline]
    fn extend_into(&self, acc: &mut Self::Extender) {
        self.fragment.extend_into(acc)
    }
}

#[cfg(feature = "std")]
#[macro_export]
#[deprecated(
    since = "2.1.0",
    note = "this implementation has been generalized and no longer requires a macro"
)]
macro_rules! impl_hex_display {
    ($fragment_type:ty) => {};
}

/// Capture the position of the current fragment
#[macro_export]
macro_rules! position {
    ($input:expr,) => {
        tag!($input, "")
    };
}

/// Capture the position of the current fragment
pub fn position<T, E>(s: T) -> IResult<T, T, E>
where
    E: ParseError<T>,
    T: InputIter + InputTake,
{
    nom::bytes::complete::take(0usize)(s)
}

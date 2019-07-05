//! nom_locate, a special input type to locate tokens
//!
//! The source code is available on [Github](https://github.com/fflorent/nom_locate)
//!
//! ## Features
//!
//! This crate exposes two cargo feature flags, `avx-accel` and `simd-accel`.
//! These correspond to the features exposed by [bytecount](https://github.com/llogiq/bytecount).
//! Compile with SSE support (available on most modern x86_64 processors) using `simd-accel`, or
//! with AVX support (which likely requires compiling for the native target CPU) with both.
//!
//! ## How to use it
//! The explanations are given in the [README](https://github.com/fflorent/nom_locate/blob/master/README.md) of the Github repository. You may also consult the [FAQ](https://github.com/fflorent/nom_locate/blob/master/FAQ.md).
//!
//! ```
//! #[macro_use]
//! extern crate nom;
//! #[macro_use]
//! extern crate nom_locate;
//!
//! use nom_locate::LocatedSpan;
//! type Span<'a> = LocatedSpan<&'a str>;
//!
//! struct Token<'a> {
//!     pub position: Span<'a>,
//!     pub foo: String,
//!     pub bar: String,
//! }
//!
//! # #[cfg(feature = "alloc")]
//! named!(parse_foobar( Span ) -> Token, do_parse!(
//!     take_until!("foo") >>
//!     position: position!() >>
//!     foo: tag!("foo") >>
//!     bar: tag!("bar") >>
//!     (Token {
//!         position: position,
//!         foo: foo.to_string(),
//!         bar: bar.to_string()
//!     })
//! ));
//!
//! # #[cfg(feature = "alloc")]
//! fn main () {
//!     let input = Span::new("Lorem ipsum \n foobar");
//!     let output = parse_foobar(input);
//!     let position = output.unwrap().1.position;
//!     assert_eq!(position, Span {
//!         offset: 14,
//!         line: 2,
//!         fragment: "",
//!         extra: (),
//!     });
//!     assert_eq!(position.get_column(), 2);
//! }
//! # #[cfg(not(feature = "alloc"))]
//! fn main() {}
//! ```
//!
//! ## Extra information
//! You can add arbitrary extra information using LocatedSpanEx.
//!
//! ``̀ 
//! use nom_locate::LocatedSpanEx;
//! type Span<'a> = LocatedSpan<&'a str, String>;
//! 
//! let input = Span::new("Lorem ipsum \n foobar", "filename");
//! let output = parse_foobar(input);
//! let extra = output.unwrap().1.extra;
//! ``̀ 


#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(all(not(feature = "std"), feature = "alloc"), feature(alloc))]

#[cfg(all(not(feature = "std"), feature = "alloc"))]
#[cfg_attr(test, macro_use)]
extern crate alloc;

extern crate bytecount;
extern crate memchr;
extern crate nom;

#[cfg(test)]
mod tests;

mod lib {
    #[cfg(feature = "std")]
    pub mod std {
        pub use std::iter::{Enumerate, Map};
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
        pub use alloc::string::{String, ToString};
        #[cfg(feature = "alloc")]
        pub use alloc::vec::Vec;
        pub use core::iter::{Enumerate, Map};
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

/// A LocatedSpan is a set of meta information about the location of a token.
/// It has the same properties as a LocatedSpanEx.
pub type LocatedSpan<T> = LocatedSpanEx<T, ()>;

/// A LocatedSpanEx is a set of meta information about the location of a token, including extra
/// information.
///
/// The `LocatedSpanEx` structure can be used as an input of the nom parsers.
/// It implements all the necessary traits for `LocatedSpanEx<&str,X>` and `LocatedSpanEx<&[u8],X>`
#[derive(PartialEq, Debug, Clone, Copy)]
pub struct LocatedSpanEx<T,X> {
    /// The offset represents the position of the fragment relatively to
    /// the input of the parser. It starts at offset 0.
    pub offset: usize,

    /// The line number of the fragment relatively to the input of the
    /// parser. It starts at line 1.
    pub line: u32,

    /// The fragment that is spanned.
    /// The fragment represents a part of the input of the parser.
    pub fragment: T,

    /// Extra information that can be embededd by the user.
    /// Example: the parsed file name
    pub extra: X,
}

impl<T: AsBytes> LocatedSpanEx<T,()> {
    /// Create a span for a particular input with default `offset` and
    /// `line` values and empty extra data.
    /// You can compute the column through the `get_column` or `get_utf8_column`
    /// methods.
    ///
    /// `offset` starts at 0, `line` starts at 1, and `column` starts at 1.
    ///
    /// # Example of use
    ///
    /// ```
    /// # extern crate nom_locate;
    /// use nom_locate::LocatedSpanEx;
    ///
    /// # fn main() {
    /// let span = LocatedSpanEx::new(b"foobar");
    ///
    /// assert_eq!(span.offset,         0);
    /// assert_eq!(span.line,           1);
    /// assert_eq!(span.get_column(),   1);
    /// assert_eq!(span.fragment,       &b"foobar"[..]);
    /// # }
    /// ```
    pub fn new(program: T) -> LocatedSpanEx<T,()> {
        LocatedSpanEx {
            line: 1,
            offset: 0,
            fragment: program,
            extra: (),
        }
    }
}

impl<T: AsBytes, X> LocatedSpanEx<T, X> {
    /// Create a span for a particular input with default `offset` and
    /// `line` values. You can compute the column through the `get_column` or `get_utf8_column`
    /// methods.
    ///
    /// `offset` starts at 0, `line` starts at 1, and `column` starts at 1.
    ///
    /// # Example of use
    ///
    /// ```
    /// # extern crate nom_locate;
    /// use nom_locate::LocatedSpanEx;
    ///
    /// # fn main() {
    /// let span = LocatedSpanEx::new_extra(b"foobar", "extra");
    ///
    /// assert_eq!(span.offset,         0);
    /// assert_eq!(span.line,           1);
    /// assert_eq!(span.get_column(),   1);
    /// assert_eq!(span.fragment,       &b"foobar"[..]);
    /// assert_eq!(span.extra,          "extra");
    /// # }
    /// ```
    pub fn new_extra(program: T, extra: X) -> LocatedSpanEx<T,X> {
        LocatedSpanEx {
            line: 1,
            offset: 0,
            fragment: program,
            extra: extra,
        }
    }

    fn get_columns_and_bytes_before(&self) -> (usize, &[u8]) {
        let self_bytes = self.fragment.as_bytes();
        let self_ptr = self_bytes.as_ptr();
        let before_self = unsafe {
            assert!(
                self.offset <= isize::max_value() as usize,
                "offset is too big"
            );
            let orig_input_ptr = self_ptr.offset(-(self.offset as isize));
            slice::from_raw_parts(orig_input_ptr, self.offset)
        };

        let column = match memchr::memrchr(b'\n', before_self) {
            None => self.offset + 1,
            Some(pos) => self.offset - pos,
        };

        (column, &before_self[self.offset - (column - 1)..])
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
    /// # use nom_locate::LocatedSpanEx;
    /// # use nom::Slice;
    /// #
    /// # fn main() {
    /// let span = LocatedSpanEx::new("foobar");
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
    /// # use nom_locate::LocatedSpanEx;
    /// # use nom::{Slice, FindSubstring};
    /// #
    /// # fn main() {
    /// let span = LocatedSpanEx::new("メカジキ");
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
    /// # use nom_locate::LocatedSpanEx;
    /// # use nom::{Slice, FindSubstring};
    /// #
    /// # fn main() {
    /// let span = LocatedSpanEx::new("メカジキ");
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

impl<T: InputLength, X> InputLength for LocatedSpanEx<T, X> {
    fn input_len(&self) -> usize {
        self.fragment.input_len()
    }
}

impl<T, X> InputTake for LocatedSpanEx<T, X>
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

impl<T, X> InputTakeAtPosition for LocatedSpanEx<T, X>
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
            None => Err(Err::Incomplete(nom::Needed::Size(1))),
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
            None => Err(Err::Incomplete(nom::Needed::Size(1))),
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

/// Implement nom::InputIter for a specific fragment type
///
/// # Parameters
/// * `$fragment_type` - The LocatedSpanEx's `fragment` type
/// * `$item` - The type of the item being iterated (a reference for fragments of type `&[T]`).
/// * `$raw_item` - The raw type of the item being iterating (dereferenced type of $item for
/// `&[T]`, otherwise same as `$item`)
/// * `$iter` - The iterator type for `iter_indices()`
/// * `$iter_elem` - The iterator type for `iter_elements()`
///
/// # Example of use
///
/// NB: This example is an extract from the nom_locate source code.
///
/// ````ignore
/// #[macro_use]
/// extern crate nom_locate;
///
/// impl_input_iter!(&'a str, char, char, CharIndices<'a>, Chars<'a>);
/// impl_input_iter!(&'a [u8], &'a u8, u8, Enumerate<Iter<'a, Self::RawItem>>,
///                  Iter<'a, Self::RawItem>);
/// ````
#[macro_export]
macro_rules! impl_input_iter {
    ($fragment_type:ty, $item:ty, $raw_item:ty, $iter:ty, $iter_elem:ty) => {
        impl<'a, X> InputIter for LocatedSpanEx<$fragment_type, X> {
            type Item = $item;
            type Iter = $iter;
            type IterElem = $iter_elem;
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
            fn slice_index(&self, count: usize) -> Option<usize> {
                self.fragment.slice_index(count)
            }
        }
    };
}

impl_input_iter!(&'a str, char, char, CharIndices<'a>, Chars<'a>);
impl_input_iter!(
    &'a [u8],
    u8,
    u8,
    Enumerate<Self::IterElem>,
    Map<Iter<'a, Self::Item>, fn(&u8) -> u8>
);

/// Implement nom::Compare for a specific fragment type.
///
/// # Parameters
/// * `$fragment_type` - The LocatedSpanEx's `fragment` type
/// * `$compare_to_type` - The type to be comparable to `LocatedSpanEx<$fragment_type, X>`
///
/// # Example of use
///
/// NB: This example is an extract from the nom_locate source code.
///
/// ````ignore
/// #[macro_use]
/// extern crate nom_locate;
/// impl_compare!(&'b str, &'a str);
/// impl_compare!(&'b [u8], &'a [u8]);
/// impl_compare!(&'b [u8], &'a str);
/// ````
#[macro_export]
macro_rules! impl_compare {
    ( $fragment_type:ty, $compare_to_type:ty ) => {
        impl<'a, 'b, X> Compare<$compare_to_type> for LocatedSpanEx<$fragment_type, X> {
            #[inline(always)]
            fn compare(&self, t: $compare_to_type) -> CompareResult {
                self.fragment.compare(t)
            }

            #[inline(always)]
            fn compare_no_case(&self, t: $compare_to_type) -> CompareResult {
                self.fragment.compare_no_case(t)
            }
        }
    };
}

impl_compare!(&'b str, &'a str);
impl_compare!(&'b [u8], &'a [u8]);
impl_compare!(&'b [u8], &'a str);

impl<A: Compare<B>, B, X, Y> Compare<LocatedSpanEx<B, X>> for LocatedSpanEx<A, Y> {
    #[inline(always)]
    fn compare(&self, t: LocatedSpanEx<B, X>) -> CompareResult {
        self.fragment.compare(t.fragment)
    }

    #[inline(always)]
    fn compare_no_case(&self, t: LocatedSpanEx<B, X>) -> CompareResult {
        self.fragment.compare_no_case(t.fragment)
    }
}

// TODO(future): replace impl_compare! with below default specialization?
// default impl<A: Compare<B>, B, X> Compare<B> for LocatedSpanEx<A, X> {
//     #[inline(always)]
//     fn compare(&self, t: B) -> CompareResult {
//         self.fragment.compare(t)
//     }
//
//     #[inline(always)]
//     fn compare_no_case(&self, t: B) -> CompareResult {
//         self.fragment.compare_no_case(t)
//     }
// }

/// Implement nom::Slice for a specific fragment type and range type.
///
/// **You'd probably better use impl_`slice_ranges`**,
/// unless you use a specific Range.
///
/// # Parameters
/// * `$fragment_type` - The LocatedSpanEx's `fragment` type
/// * `$range_type` - The range type to be use with `slice()`.
/// * `$can_return_self` - A bool-returning lambda telling whether we
///    can avoid creating a new `LocatedSpanEx`. If unsure, use `|_| false`.
///
/// # Example of use
///
/// NB: This example is an extract from the nom_locate source code.
///
/// ````ignore
/// #[macro_use]
/// extern crate nom_locate;
///
/// #[macro_export]
/// macro_rules! impl_slice_ranges {
///     ( $fragment_type:ty ) => {
///         impl_slice_range! {$fragment_type, Range<usize>, |_| false }
///         impl_slice_range! {$fragment_type, RangeTo<usize>, |_| false }
///         impl_slice_range! {$fragment_type, RangeFrom<usize>, |range:&RangeFrom<usize>| range.start == 0}
///         impl_slice_range! {$fragment_type, RangeFull, |_| true}
///     }
/// }
///
/// ````
#[macro_export]
macro_rules! impl_slice_range {
    ( $fragment_type:ty, $range_type:ty, $can_return_self:expr ) => {
        impl<'a, X: Clone> Slice<$range_type> for LocatedSpanEx<$fragment_type, X> {
            fn slice(&self, range: $range_type) -> Self {
                if $can_return_self(&range) {
                    return self.clone();
                }
                let next_fragment = self.fragment.slice(range);
                let consumed_len = self.fragment.offset(&next_fragment);
                if consumed_len == 0 {
                    return LocatedSpanEx {
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

                LocatedSpanEx {
                    line: next_line,
                    offset: next_offset,
                    fragment: next_fragment,
                    extra: self.extra.clone(),
                }
            }
        }
    };
}

/// Implement nom::Slice for a specific fragment type and for these types of range:
/// * `Range<usize>`
/// * `RangeTo<usize>`
/// * `RangeFrom<usize>`
/// * `RangeFull`
///
/// # Parameters
/// * `$fragment_type` - The LocatedSpanEx's `fragment` type
///
/// # Example of use
///
/// NB: This example is an extract from the nom_locate source code.
///
/// ````ignore
/// #[macro_use]
/// extern crate nom_locate;
///
/// impl_slice_ranges! {&'a str}
/// impl_slice_ranges! {&'a [u8]}
/// ````
#[macro_export]
macro_rules! impl_slice_ranges {
    ( $fragment_type:ty ) => {
        impl_slice_range! {$fragment_type, Range<usize>, |_| false }
        impl_slice_range! {$fragment_type, RangeTo<usize>, |_| false }
        impl_slice_range! {$fragment_type, RangeFrom<usize>, |range:&RangeFrom<usize>| range.start == 0}
        impl_slice_range! {$fragment_type, RangeFull, |_| true}
    }
}

impl_slice_ranges! {&'a str}
impl_slice_ranges! {&'a [u8]}

impl<Fragment: FindToken<Token>, Token, X> FindToken<Token> for LocatedSpanEx<Fragment, X> {
    fn find_token(&self, token: Token) -> bool {
        self.fragment.find_token(token)
    }
}

impl<'a, T, X> FindSubstring<&'a str> for LocatedSpanEx<T, X>
where
    T: FindSubstring<&'a str>,
{
    #[inline]
    fn find_substring(&self, substr: &'a str) -> Option<usize> {
        self.fragment.find_substring(substr)
    }
}

impl<R: FromStr, T, X> ParseTo<R> for LocatedSpanEx<T, X>
where
    T: ParseTo<R>,
{
    #[inline]
    fn parse_to(&self) -> Option<R> {
        self.fragment.parse_to()
    }
}

impl<T, X> Offset for LocatedSpanEx<T, X> {
    fn offset(&self, second: &Self) -> usize {
        let fst = self.offset;
        let snd = second.offset;

        snd - fst
    }
}

#[cfg(feature = "alloc")]
impl<T: ToString, X> ToString for LocatedSpanEx<T, X> {
    #[inline]
    fn to_string(&self) -> String {
        self.fragment.to_string()
    }
}

/// Implement nom::ExtendInto for a specific fragment type.
///
/// # Parameters
/// * `$fragment_type` - The LocatedSpanEx's `fragment` type
/// * `$item` - The type of the item being iterated (a reference for fragments of type `&[T]`).
/// * `$extender` - The type of the Extended.
///
/// # Example of use
///
/// NB: This example is an extract from the nom_locate source code.
///
/// ````ignore
/// #[macro_use]
/// extern crate nom_locate;
///
/// impl_extend_into!(&'a str, char, String);
/// impl_extend_into!(&'a [u8], u8, Vec<u8>);
/// ````
#[macro_export]
macro_rules! impl_extend_into {
    ($fragment_type:ty, $item:ty, $extender:ty) => {
        impl<'a, X> ExtendInto for LocatedSpanEx<$fragment_type, X> {
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
impl_extend_into!(&'a str, char, String);
#[cfg(feature = "alloc")]
impl_extend_into!(&'a [u8], u8, Vec<u8>);

#[macro_export]
macro_rules! impl_hex_display {
    ($fragment_type:ty) => {
        #[cfg(feature = "alloc")]
        impl<'a, X> nom::HexDisplay for LocatedSpanEx<$fragment_type, X> {
            fn to_hex(&self, chunk_size: usize) -> String {
                self.fragment.to_hex(chunk_size)
            }

            fn to_hex_from(&self, chunk_size: usize, from: usize) -> String {
                self.fragment.to_hex_from(chunk_size, from)
            }
        }
    };
}

impl_hex_display!(&'a str);
impl_hex_display!(&'a [u8]);

/// Capture the position of the current fragment

#[macro_export]
macro_rules! position {
    ($input:expr,) => {
        tag!($input, "")
    };
}

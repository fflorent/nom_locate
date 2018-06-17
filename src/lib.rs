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
//! ````
//! #[macro_use]
//! extern crate nom;
//! #[macro_use]
//! extern crate nom_locate;
//!
//! use nom::types::CompleteStr;
//! use nom_locate::LocatedSpan;
//! type Span<'a> = LocatedSpan<CompleteStr<'a>>;
//!
//! struct Token<'a> {
//!     pub position: Span<'a>,
//!     pub foo: String,
//!     pub bar: String,
//! }
//!
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
//! fn main () {
//!     let input = Span::new(CompleteStr("Lorem ipsum \n foobar"));
//!     let output = parse_foobar(input);
//!     let position = output.unwrap().1.position;
//!     assert_eq!(position, Span {
//!         offset: 14,
//!         line: 2,
//!         fragment: CompleteStr("")
//!     });
//!     assert_eq!(position.get_column(), 2);
//! }
//! ````
extern crate bytecount;
extern crate memchr;
extern crate nom;

#[cfg(test)]
mod tests;

use std::iter::{Enumerate, Map};
use std::ops::{Range, RangeFrom, RangeFull, RangeTo};
use std::slice::Iter;
use std::str::{CharIndices, Chars, FromStr};

use memchr::Memchr;
use nom::{AsBytes, Compare, CompareResult, FindSubstring, FindToken, InputIter, InputLength,
          Offset, ParseTo, Slice, InputTake, InputTakeAtPosition, AtEof, ExtendInto,
          IResult, ErrorKind, Err, Context};
use nom::types::{CompleteByteSlice, CompleteStr};
use bytecount::{naive_num_chars, num_chars};

/// A LocatedSpan is a set of meta information about the location of a token.
///
/// The `LocatedSpan` structure can be used as an input of the nom parsers.
/// It implements all the necessary traits for `LocatedSpan<&str>` and `LocatedSpan<&[u8]>`
#[derive(PartialEq, Debug, Clone, Copy)]
pub struct LocatedSpan<T> {
    /// The offset represents the position of the fragment relatively to
    /// the input of the parser. It starts at offset 0.
    pub offset: usize,

    /// The line number of the fragment relatively to the input of the
    /// parser. It starts at line 1.
    pub line: u32,

    /// The fragment that is spanned.
    /// The fragment represents a part of the input of the parser.
    pub fragment: T,
}

impl<T: AsBytes> LocatedSpan<T> {
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
    /// use nom_locate::LocatedSpan;
    ///
    /// # fn main() {
    /// let span = LocatedSpan::new(b"foobar");
    ///
    /// assert_eq!(span.offset,         0);
    /// assert_eq!(span.line,           1);
    /// assert_eq!(span.get_column(),   1);
    /// assert_eq!(span.fragment,       &b"foobar"[..]);
    /// # }
    /// ```
    pub fn new(program: T) -> LocatedSpan<T> {
        LocatedSpan {
            line: 1,
            offset: 0,
            fragment: program,
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
            std::slice::from_raw_parts(orig_input_ptr, self.offset)
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

impl<T: InputLength> InputLength for LocatedSpan<T> {
    fn input_len(&self) -> usize {
        self.fragment.input_len()
    }
}

impl<T: AtEof> AtEof for LocatedSpan<T> {
    fn at_eof(&self) -> bool {
        self.fragment.at_eof()
    }
}

impl<T> InputTake for LocatedSpan<T> where Self: Slice<RangeFrom<usize>> + Slice<RangeTo<usize>> {
    fn take(&self, count: usize) -> Self {
        self.slice(..count)
    }

    fn take_split(&self, count: usize) -> (Self, Self) {
        (self.slice(count..), self.slice(..count))
    }
}

impl<T> InputTakeAtPosition for LocatedSpan<T>
where
    T: InputTakeAtPosition + InputLength,
    Self: Slice<RangeFrom<usize>> + Slice<RangeTo<usize>> + Clone,
{
    type Item = <T as InputTakeAtPosition>::Item;

    fn split_at_position<P>(&self, predicate: P) -> IResult<Self, Self, u32>
    where
        P: Fn(Self::Item) -> bool
    {
        self.fragment.split_at_position(predicate)
            .map(|(_i, o)| {
                let split = o.input_len();
                (self.slice(split..), self.slice(..split))
            })
            .map_err(|e| {
                match e {
                    Err::Error(Context::Code(_, e)) |
                    Err::Failure(Context::Code(_, e)) => Err::Error(Context::Code(self.clone(), e)),
                    Err::Incomplete(needed) => Err::Incomplete(needed),
                    _ => unimplemented!("nom_locate didn't think Err::List was used in InputTakeAtPosition"),
                }
            })
    }

    fn split_at_position1<P>(&self, predicate: P, e: ErrorKind<u32>) -> IResult<Self, Self, u32>
    where
        P: Fn(Self::Item) -> bool
    {
        self.fragment.split_at_position1(predicate, e)
            .map(|(_i, o)| {
                let split = o.input_len();
                (self.slice(split..), self.slice(..split))
            })
            .map_err(|e| {
                match e {
                    Err::Error(Context::Code(_, e)) |
                    Err::Failure(Context::Code(_, e)) => Err::Error(Context::Code(self.clone(), e)),
                    Err::Incomplete(needed) => Err::Incomplete(needed),
                    _ => unimplemented!("nom_locate didn't think Err::List was used in InputTakeAtPosition"),
                }
            })
    }
}

/// Implement nom::InputIter for a specific fragment type
///
/// # Parameters
/// * `$fragment_type` - The LocatedSpan's `fragment` type
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
    ($fragment_type:ty, $item:ty, $raw_item:ty, $iter:ty, $iter_elem:ty) => (
        impl<'a> InputIter for LocatedSpan<$fragment_type> {
            type Item     = $item;
            type RawItem  = $raw_item;
            type Iter     = $iter;
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
            fn position<P>(&self, predicate: P) -> Option<usize> where P: Fn(Self::RawItem) -> bool {
                self.fragment.position(predicate)
            }
            #[inline]
            fn slice_index(&self, count:usize) -> Option<usize> {
                self.fragment.slice_index(count)
            }
        }
    )
}

impl_input_iter!(&'a str, char, char, CharIndices<'a>, Chars<'a>);
impl_input_iter!(
    &'a [u8],
    u8,
    u8,
    Enumerate<Self::IterElem>,
    Map<Iter<'a, Self::Item>, fn(&u8) -> u8>
);
impl_input_iter!(CompleteStr<'a>, char, char, CharIndices<'a>, Chars<'a>);
impl_input_iter!(
    CompleteByteSlice<'a>,
    u8,
    u8,
    Enumerate<Self::IterElem>,
    Map<Iter<'a, Self::Item>, fn(&u8) -> u8>
);

/// Implement nom::Compare for a specific fragment type.
///
/// # Parameters
/// * `$fragment_type` - The LocatedSpan's `fragment` type
/// * `$compare_to_type` - The type to be comparable to `LocatedSpan<$fragment_type>`
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
        impl<'a,'b> Compare<$compare_to_type> for LocatedSpan<$fragment_type> {
            #[inline(always)]
            fn compare(&self, t: $compare_to_type) -> CompareResult {
                self.fragment.compare(t)
            }

            #[inline(always)]
            fn compare_no_case(&self, t: $compare_to_type) -> CompareResult {
                self.fragment.compare_no_case(t)
            }
        }
    }
}

impl_compare!(&'b str, &'a str);
impl_compare!(CompleteStr<'b>, &'a str);
impl_compare!(&'b [u8], &'a [u8]);
impl_compare!(CompleteByteSlice<'b>, &'a [u8]);
impl_compare!(&'b [u8], &'a str);
impl_compare!(CompleteByteSlice<'b>, &'a str);

impl<A: Compare<B>, B> Compare<LocatedSpan<B>> for LocatedSpan<A> {
    #[inline(always)]
    fn compare(&self, t: LocatedSpan<B>) -> CompareResult {
        self.fragment.compare(t.fragment)
    }

    #[inline(always)]
    fn compare_no_case(&self, t: LocatedSpan<B>) -> CompareResult {
        self.fragment.compare_no_case(t.fragment)
    }
}

// TODO(future): replace impl_compare! with below default specialization?
// default impl<A: Compare<B>, B> Compare<B> for LocatedSpan<A> {
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
/// * `$fragment_type` - The LocatedSpan's `fragment` type
/// * `$range_type` - The range type to be use with `slice()`.
/// * `$can_return_self` - A bool-returning lambda telling whether we
///    can avoid creating a new `LocatedSpan`. If unsure, use `|_| false`.
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
        impl<'a> Slice<$range_type> for LocatedSpan<$fragment_type> {
            fn slice(&self, range: $range_type) -> Self {
                if $can_return_self(&range) {
                    return *self;
                }
                let next_fragment = self.fragment.slice(range);
                let consumed_len = self.fragment.offset(&next_fragment);
                if consumed_len == 0 {
                    return LocatedSpan {
                        line: self.line,
                        offset: self.offset,
                        fragment: next_fragment
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
                    fragment: next_fragment
                }
            }
        }
    }
}

/// Implement nom::Slice for a specific fragment type and for these types of range:
/// * `Range<usize>`
/// * `RangeTo<usize>`
/// * `RangeFrom<usize>`
/// * `RangeFull`
///
/// # Parameters
/// * `$fragment_type` - The LocatedSpan's `fragment` type
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
impl_slice_ranges! {CompleteStr<'a>}
impl_slice_ranges! {CompleteByteSlice<'a>}

impl<Fragment: FindToken<Token>, Token> FindToken<Token> for LocatedSpan<Fragment> {
    fn find_token(&self, token: Token) -> bool {
        self.fragment.find_token(token)
    }
}

impl<'a, T> FindSubstring<&'a str> for LocatedSpan<T>
where
    T: FindSubstring<&'a str>,
{
    #[inline]
    fn find_substring(&self, substr: &'a str) -> Option<usize> {
        self.fragment.find_substring(substr)
    }
}

impl<R: FromStr, T> ParseTo<R> for LocatedSpan<T>
where
    T: ParseTo<R>,
{
    #[inline]
    fn parse_to(&self) -> Option<R> {
        self.fragment.parse_to()
    }
}

impl<T> Offset for LocatedSpan<T> {
    fn offset(&self, second: &Self) -> usize {
        let fst = self.offset;
        let snd = second.offset;

        snd - fst
    }
}

impl<T: ToString> ToString for LocatedSpan<T> {
    #[inline]
    fn to_string(&self) -> String {
        self.fragment.to_string()
    }
}

/// Implement nom::ExtendInto for a specific fragment type.
///
/// # Parameters
/// * `$fragment_type` - The LocatedSpan's `fragment` type
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
/// impl_extend_into!(CompleteStr<'a>, char, String);
/// impl_extend_into!(&'a [u8], u8, Vec<u8>);
/// impl_extend_into!(CompleteByteSlice<'a>, u8, Vec<u8>);
/// ````
#[macro_export]
macro_rules! impl_extend_into {
    ($fragment_type:ty, $item:ty, $extender:ty) => (
        impl<'a> ExtendInto for LocatedSpan<$fragment_type> {
            type Item     = $item;
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
    )
}

impl_extend_into!(&'a str, char, String);
impl_extend_into!(CompleteStr<'a>, char, String);
impl_extend_into!(&'a [u8], u8, Vec<u8>);
impl_extend_into!(CompleteByteSlice<'a>, u8, Vec<u8>);

#[macro_export]
macro_rules! impl_hex_display {
    ($fragment_type:ty) => (
		impl<'a> nom::HexDisplay for LocatedSpan<$fragment_type> {
			fn to_hex(&self, chunk_size: usize) -> String {
				self.fragment.to_hex(chunk_size)
			}

			fn to_hex_from(&self, chunk_size: usize, from: usize) -> String {
				self.fragment.to_hex_from(chunk_size, from)
			}
		}
	)
}

impl_hex_display!(&'a str);
impl_hex_display!(CompleteStr<'a>);
impl_hex_display!(&'a [u8]);
impl_hex_display!(CompleteByteSlice<'a>);


/// Capture the position of the current fragment

#[macro_export]
macro_rules! position {
    ($input:expr,) => (
        tag!($input, "")
     );
}

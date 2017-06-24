//! nom_locate, a special input type to locate tokens
//!
//! The source code is available on [Github](https://github.com/fflorent/nom_locate)
//!
//! ## How to use it
//! The explanations are given in the [README](https://github.com/fflorent/nom_locate/blob/master/README.md) of the Github repository. You may also consult the [FAQ](https://github.com/fflorent/nom_locate/blob/master/FAQ.md).
//!
//! ````
//! #[macro_use]
//! extern crate nom;
//! #[macro_use(position)]
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
//!     let input = Span::new("Lorem ipsum \n foobar");
//!     let output = parse_foobar(input);
//!     let position = output.unwrap().1.position;
//!     assert_eq!(position, Span {
//!         offset: 14,
//!         line: 2,
//!         fragment: ""
//!     });
//!     assert_eq!(position.get_column(), 2);
//! }
//! ````
extern crate nom;
extern crate memchr;

#[cfg(test)]
mod tests;

use std::iter::Enumerate;
use std::ops::{Range, RangeTo, RangeFrom, RangeFull};
use std::slice::Iter;
use std::str::{CharIndices, Chars, FromStr, Utf8Error};

use memchr::Memchr;
use nom::{
    InputLength, Slice, InputIter, Compare, CompareResult,
    Offset, FindToken, FindSubstring, ParseTo, AsBytes
};

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
    /// `line` values. You can compute the column through the `get_column` or `get_column_utf8`
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
             fragment: program
         }
    }

    fn get_columns_and_bytes_before(&self) -> (usize, &[u8]) {
        let self_bytes = self.fragment.as_bytes();
        let self_ptr = self_bytes.as_ptr();
        let before_self = unsafe {
            assert!(self.offset <= isize::max_value() as usize, "offset is too big");
            let orig_input_ptr = self_ptr.offset(-(self.offset as isize));
            std::slice::from_raw_parts(orig_input_ptr, self.offset)
        };

        let column = match memchr::memrchr(b'\n', before_self) {
            None => self.offset + 1,
            Some(pos) => {
                self.offset - pos
            }
        };

        (column, &before_self[self.offset - (column - 1)..])
    }

    /// Return the column index, assuming 1 byte = 1 column.
    ///
    /// Use it for ascii text, or use get_column_utf8 for UTF8.
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

    /// Return the column index for a UTF8 text.
    ///
    /// **Caution**: that's a rather slow method. Prefer using
    /// `get_column()` if your input is an ASCII-only text.
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
    /// assert_eq!(span.slice(indexOf3dKanji..).get_column_utf8(), Ok(3));
    /// # }
    /// ```
    pub fn get_column_utf8(&self) -> Result<usize, Utf8Error> {
        let before_self = self.get_columns_and_bytes_before().1;
        Ok(std::str::from_utf8(before_self)?
            .chars()
            .count() + 1)
    }
}

impl<T: InputLength> InputLength for LocatedSpan<T> {
    fn input_len(&self) -> usize {
        self.fragment.input_len()
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
impl_input_iter!(&'a [u8], &'a u8, u8, Enumerate<Iter<'a, Self::RawItem>>,
                 Iter<'a, Self::RawItem>);


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
impl_compare!(&'b [u8], &'a [u8]);
impl_compare!(&'b [u8], &'a str);

/// Implement nom::Slice for a specific fragment type and range type.
///
/// **You'd probably better use impl_`slice_ranges`**,
/// unless you use a specific Range.
///
/// # Parameters
/// * `$fragment_type` - The LocatedSpan's `fragment` type
/// * `$range_type` - The range type to be use with `slice()`.
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
///         impl_slice_range! {$fragment_type, Range<usize>}
///         impl_slice_range! {$fragment_type, RangeTo<usize>}
///         impl_slice_range! {$fragment_type, RangeFrom<usize>}
///         impl_slice_range! {$fragment_type, RangeFull}
///     }
/// }
///
/// ````
#[macro_export]
macro_rules! impl_slice_range {
    ( $fragment_type:ty, $range_type:ty ) => {
        impl<'a> Slice<$range_type> for LocatedSpan<$fragment_type> {
            fn slice(&self, range: $range_type) -> Self {
                let next_fragment = self.fragment.slice(range);
                if next_fragment == self.fragment {
                    return *self;
                }
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
        impl_slice_range! {$fragment_type, Range<usize>}
        impl_slice_range! {$fragment_type, RangeTo<usize>}
        impl_slice_range! {$fragment_type, RangeFrom<usize>}
        impl_slice_range! {$fragment_type, RangeFull}
    }
}

impl_slice_ranges! {&'a str}
impl_slice_ranges! {&'a [u8]}

/// Implement nom::FindToken for a specific token type.
///
/// # Parameters
/// * `$for_type` - The token type.
/// * `$fragment_type` - The LocatedSpan's `fragment` type which has to be searchable.
///
/// # Example of use
///
/// NB: This example is an extract from the nom_locate source code.
///
/// ````ignore
/// #[macro_use]
/// extern crate nom_locate;
///
/// impl_find_token! { char, &'a str}
///
/// impl_find_token! { u8, &'a str}
/// impl_find_token! { &'b u8, &'a str}
///
/// impl_find_token! { u8, &'a [u8]}
/// impl_find_token! { &'b u8, &'a [u8]}
/// ````
#[macro_export]
macro_rules! impl_find_token {
    ( $for_type:ty, $fragment_type:ty) => {
        impl<'a, 'b> FindToken<LocatedSpan<$fragment_type>> for $for_type {
            fn find_token(&self, input: LocatedSpan<$fragment_type>) -> bool {
                self.find_token(input.fragment)
            }
        }
    }
}

impl_find_token! { char, &'a str}

impl_find_token! { u8, &'a str}
impl_find_token! { &'b u8, &'a str}

impl_find_token! { u8, &'a [u8]}
impl_find_token! { &'b u8, &'a [u8]}


impl<'a, T> FindSubstring<&'a str> for LocatedSpan<T>
    where T: FindSubstring<&'a str> {

    #[inline]
    fn find_substring(&self, substr: &'a str) -> Option<usize> {
        self.fragment.find_substring(substr)
    }
}

impl<R: FromStr, T> ParseTo<R> for LocatedSpan<T>
    where T: ParseTo<R> {

    #[inline]
    fn parse_to(&self) -> Option<R> {
        self.fragment.parse_to()
    }
}

/// Implement nom::Offset for a specific fragment type.
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
/// impl_offset! {&'a str}
/// impl_offset! {&'a [u8]}
/// ````
#[macro_export]
macro_rules! impl_offset {
    ( $fragment_type:ty ) => {
        #[cfg(not(feature = "core"))]
        impl<'a> Offset for LocatedSpan<$fragment_type> {
            fn offset(&self, second: &LocatedSpan<$fragment_type>) -> usize {
                    let fst = self.fragment.as_ptr();
                    let snd = second.fragment.as_ptr();

                    snd as usize - fst as usize
            }
        }
    }
}

impl_offset! {&'a str}
impl_offset! {&'a [u8]}

impl<T: ToString> ToString for LocatedSpan<T> {
    #[inline]
    fn to_string(&self) -> String {
        self.fragment.to_string()
    }
}

/// Capture the position of the current fragment

#[macro_export]
macro_rules! position {
    ($input:expr,) => (
        tag!($input, "")
     );
}

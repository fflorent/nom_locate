extern crate nom;
extern crate memchr;

#[cfg(test)]
mod tests;

use std::iter::Enumerate;
use std::ops::{Range, RangeTo, RangeFrom, RangeFull};
use std::slice::Iter;
use std::str::CharIndices;
use std::str::Chars;
use std::str::{FromStr, Utf8Error};


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

    /// The column number of the fragment relatively to the input of the
    /// parser. It starts at column 0.
    // FIXME allow starting at 1
    pub column: u32,

    /// The fragment that is spanned.
    pub fragment: T,
}

impl<T> LocatedSpan<T> {

    /// Create a span for a particular input with default `offset`,
    /// `line`, and `column` values.
    ///
    /// `offset` starts at 0, `line` starts at 1, and `column` starts at 0.
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
    /// assert_eq!(span.offset,     0);
    /// assert_eq!(span.line,       1);
    /// assert_eq!(span.column,     0);
    /// assert_eq!(span.fragment,   &b"foobar"[..]);
    /// # }
    /// ```
    pub fn new(program: T) -> LocatedSpan<T> {
         LocatedSpan {
             line: 1,
             column: 0,
             offset: 0,
             fragment: program
         }
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
/// compare_impl!(&'b str, &'a str);
/// compare_impl!(&'b [u8], &'a [u8]);
/// compare_impl!(&'b [u8], &'a str);
/// ````
#[macro_export]
macro_rules! compare_impl {
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

compare_impl!(&'b str, &'a str);
compare_impl!(&'b [u8], &'a [u8]);
compare_impl!(&'b [u8], &'a str);

/// Implement nom::Slice for a specific fragment type and range type.
///
/// **You'd probably better use `slice_ranges_impl`**,
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
/// macro_rules! slice_ranges_impl {
///     ( $fragment_type:ty ) => {
///         slice_range_impl! {$fragment_type, Range<usize>}
///         slice_range_impl! {$fragment_type, RangeTo<usize>}
///         slice_range_impl! {$fragment_type, RangeFrom<usize>}
///         slice_range_impl! {$fragment_type, RangeFull}
///     }
/// }
///
/// ````
#[macro_export]
macro_rules! slice_range_impl {
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
                        column: self.column,
                        line: self.line,
                        offset: self.offset,
                        fragment: next_fragment
                    };
                }

                let consumed = self.fragment.slice(..consumed_len);
                let next_offset = self.offset + consumed_len;

                let consumed_as_bytes = consumed.as_bytes();
                let mut iter = Memchr::new(b'\n', consumed_as_bytes);
                let (number_of_lines, next_column) = match iter.next_back() {
                    None => (0, self.column + consumed.count_utf8() as u32),
                    Some(position) => {
                        let next_column = self.fragment.slice(position..consumed_len)
                            .count_utf8() as u32;

                        (iter.count() as u32 + 1, next_column)
                    }
                };
                let next_line = self.line + number_of_lines;

                LocatedSpan {
                    column: next_column,
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
/// slice_ranges_impl! {&'a str}
/// slice_ranges_impl! {&'a [u8]}
/// ````
#[macro_export]
macro_rules! slice_ranges_impl {
    ( $fragment_type:ty ) => {
        slice_range_impl! {$fragment_type, Range<usize>}
        slice_range_impl! {$fragment_type, RangeTo<usize>}
        slice_range_impl! {$fragment_type, RangeFrom<usize>}
        slice_range_impl! {$fragment_type, RangeFull}
    }
}

slice_ranges_impl! {&'a str}
slice_ranges_impl! {&'a [u8]}

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
/// find_token_impl! { char, &'a str}
///
/// find_token_impl! { u8, &'a str}
/// find_token_impl! { &'b u8, &'a str}
///
/// find_token_impl! { u8, &'a [u8]}
/// find_token_impl! { &'b u8, &'a [u8]}
/// ````
#[macro_export]
macro_rules! find_token_impl {
    ( $for_type:ty, $fragment_type:ty) => {
        impl<'a, 'b> FindToken<LocatedSpan<$fragment_type>> for $for_type {
            fn find_token(&self, input: LocatedSpan<$fragment_type>) -> bool {
                self.find_token(input.fragment)
            }
        }
    }
}

find_token_impl! { char, &'a str}

find_token_impl! { u8, &'a str}
find_token_impl! { &'b u8, &'a str}

find_token_impl! { u8, &'a [u8]}
find_token_impl! { &'b u8, &'a [u8]}


impl<'a, T> FindSubstring<&'a str> for LocatedSpan<T>
    where T: FindSubstring<&'a str> {

    fn find_substring(&self, substr: &'a str) -> Option<usize> {
        self.fragment.find_substring(substr)
    }
}

impl<R: FromStr, T> ParseTo<R> for LocatedSpan<T>
    where T: ParseTo<R> {

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
/// offset_impl! {&'a str}
/// offset_impl! {&'a [u8]}
/// ````
#[macro_export]
macro_rules! offset_impl {
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

offset_impl! {&'a str}
offset_impl! {&'a [u8]}

/// Trait to count utf8 chars
pub trait CountUtf8Chars {
    /// Return the number of UTF-8 chars.
    ///
    /// # Example of use
    /// ````
    /// # extern crate nom_locate;
    /// use nom_locate::CountUtf8Chars;
    ///
    /// # fn main() {
    /// assert_eq!("un œuf éclot".len(), 14); // That's not the number of characters
    /// assert_eq!("un œuf éclot".count_utf8(), 12);
    /// # }
    /// ````
    fn count_utf8(&self) -> usize;
}

impl<'a> CountUtf8Chars for &'a str {
    fn count_utf8(&self) -> usize {
        self.chars().count()
    }
}

impl<'a> CountUtf8Chars for &'a [u8] {
    fn count_utf8(&self) -> usize {
        std::str::from_utf8(self)
            .expect("The slice should contain UTF-8 chars only")
            .count_utf8()
    }
}

impl<T: ToString> ToString for LocatedSpan<T> {
    fn to_string(&self) -> String {
        self.fragment.to_string()
    }
}

extern crate nom;
extern crate memchr;

#[cfg(test)]
mod tests;

use std::ops::{Range, RangeTo, RangeFrom, RangeFull};
use std::str::{FromStr, Utf8Error};
use std::iter::Enumerate;
use std::slice::Iter;

use memchr::Memchr;
use nom::{
    InputLength, Slice, InputIter, Compare, CompareResult,
    Offset, FindToken, FindSubstring, ParseTo, AsBytes
};

use std::str::Chars;
use std::str::CharIndices;

// FIXME rename it. LocatedChunk? (does chunk means disjoint?)
#[derive(PartialEq, Debug, Clone, Copy)]
pub struct LocatedSpan<T> {
    pub column: usize,
    pub line: usize,
    pub index: usize,
    pub slice: T,
}

impl<T: InputLength> LocatedSpan<T> {
    pub fn new(program: T) -> LocatedSpan<T> {
         LocatedSpan {
             line: 1,
             column: 0, // FIXME Specific for EsTree
             index: 0,
             slice: program
         }
    }
}

impl<T: InputLength> InputLength for LocatedSpan<T> {
    fn input_len(&self) -> usize {
        self.slice.input_len()
    }
}

macro_rules! impl_input_iter {
    ($for_type:ty, $item:ty, $raw_item:ty, $iter:ty, $iter_elem:ty) => (
        impl<'a> InputIter for LocatedSpan<$for_type> {
            type Item     = $item;
            type RawItem  = $raw_item;
            type Iter     = $iter;
            type IterElem = $iter_elem;
            #[inline]
            fn iter_indices(&self) -> Self::Iter {
                self.slice.iter_indices()
            }
            #[inline]
            fn iter_elements(&self) -> Self::IterElem {
              self.slice.iter_elements()
            }
            fn position<P>(&self, predicate: P) -> Option<usize> where P: Fn(Self::RawItem) -> bool {
                self.slice.position(predicate)
            }
            #[inline]
            fn slice_index(&self, count:usize) -> Option<usize> {
                self.slice.slice_index(count)
            }
        }
    )
}

impl_input_iter!(&'a str, char, char, CharIndices<'a>, Chars<'a>);
impl_input_iter!(&'a [u8], &'a u8, u8, Enumerate<Iter<'a, Self::RawItem>>,
                 Iter<'a, Self::RawItem>);


macro_rules! compare_impl {
    ( $for_type:ty, $compare_to_type:ty ) => {
        impl<'a,'b> Compare<$compare_to_type> for $for_type {
            #[inline(always)]
            fn compare(&self, t: $compare_to_type) -> CompareResult {
                self.slice.compare(t)
            }

            #[inline(always)]
            fn compare_no_case(&self, t: $compare_to_type) -> CompareResult {
                self.slice.compare_no_case(t)
            }
        }
    }
}

compare_impl!(LocatedSpan<&'b str>, &'a str);
compare_impl!(LocatedSpan<&'b [u8]>, &'a [u8]);
compare_impl!(LocatedSpan<&'b [u8]>, &'a str);

macro_rules! slice_range_impl {
    ( $for_type:ty, $range_type:ty ) => {
        impl<'a> Slice<$range_type> for $for_type {
            fn slice(&self, range: $range_type) -> Self {
                let next_slice = self.slice.slice(range);
                if next_slice == self.slice {
                    return *self;
                }
                let consumed_len = self.slice.offset(&next_slice);
                if consumed_len == 0 {
                    return LocatedSpan {
                        column: self.column,
                        line: self.line,
                        index: self.index,
                        slice: next_slice
                    };
                }

                let consumed = self.slice.slice(..consumed_len);
                let next_index = self.index + consumed_len;

                let consumed_as_bytes = consumed.as_bytes();
                let mut iter = Memchr::new(b'\n', consumed_as_bytes);
                let (number_of_lines, next_column) = match iter.next_back() {
                    None => (0, self.column + consumed.count_utf8().unwrap()),
                    Some(position) => (iter.count() + 1, self.slice.slice(position..consumed_len).count_utf8().unwrap())
                };
                let next_line = self.line + number_of_lines;

                LocatedSpan {
                    column: next_column,
                    line: next_line,
                    index: next_index,
                    slice: next_slice
                }
            }
        }
    }
}

macro_rules! slice_ranges_impl {
    ( $for_type:ty ) => {
        slice_range_impl! {$for_type, Range<usize>}
        slice_range_impl! {$for_type, RangeTo<usize>}
        slice_range_impl! {$for_type, RangeFrom<usize>}
        slice_range_impl! {$for_type, RangeFull}
    }
}

slice_ranges_impl! {LocatedSpan<&'a str>}
slice_ranges_impl! {LocatedSpan<&'a [u8]>}

macro_rules! find_token_impl {
    ( $for_type:ty, $ty:ty, [$($lifetimes:tt),*] ) => {
        impl<'a$(, $lifetimes)*> FindToken<$ty> for $for_type {
            fn find_token(&self, input: $ty) -> bool {
                self.find_token(input.slice)
            }
        }
    }
}

find_token_impl! { char, LocatedSpan<&'a str>, [] }

find_token_impl! { u8, LocatedSpan<&'a str>, [] }
find_token_impl! { &'b u8, LocatedSpan<&'a str>, ['b] }

find_token_impl! { u8, LocatedSpan<&'a [u8]>, [] }
find_token_impl! { &'b u8, LocatedSpan<&'a [u8]>, ['b] }

impl<'a, T> FindSubstring<&'a str> for LocatedSpan<T>
    where T: FindSubstring<&'a str> {

    fn find_substring(&self, substr: &'a str) -> Option<usize> {
        self.slice.find_substring(substr)
    }
}

impl<R: FromStr, T> ParseTo<R> for LocatedSpan<T>
    where T: ParseTo<R> {

    fn parse_to(&self) -> Option<R> {
        self.slice.parse_to()
    }
}

macro_rules! offset_impl {
    ( $for_slice_type:ty ) => {
        #[cfg(not(feature = "core"))]
        impl<'a> Offset for LocatedSpan<$for_slice_type> {
            fn offset(&self, second: &LocatedSpan<$for_slice_type>) -> usize {
                    let fst = self.slice.as_ptr();
                    let snd = second.slice.as_ptr();

                    snd as usize - fst as usize
            }
        }
    }
}

offset_impl! {&'a str}
offset_impl! {&'a [u8]}

pub trait CountUtf8Chars {
    fn count_utf8(&self) -> Result<usize, Utf8Error>;
}

impl<'a> CountUtf8Chars for &'a str {
    fn count_utf8(&self) -> Result<usize, Utf8Error> {
        Ok(self.chars().count())
    }
}

impl<'a> CountUtf8Chars for &'a [u8] {
    fn count_utf8(&self) -> Result<usize, Utf8Error> {
        std::str::from_utf8(self)?.count_utf8()
    }
}

impl<T: ToString> ToString for LocatedSpan<T> {
    fn to_string(&self) -> String {
        self.slice.to_string()
    }
}

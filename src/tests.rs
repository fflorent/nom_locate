use super::LocatedSpan;
use nom::{
    Slice, InputIter, Compare, CompareResult,
    FindToken, FindSubstring, ParseTo, Offset
};

type StrSpan<'a> = LocatedSpan<&'a str>;
type BytesSpan<'a> = LocatedSpan<&'a [u8]>;

#[test]
fn it_should_call_new_for_u8_successfully() {
    let input  = &b"foobar"[..];
    let output = BytesSpan {
        offset : 0,
        line  : 1,
        fragment : input
    };

    assert_eq!(BytesSpan::new(input), output);
}

#[test]
fn it_should_call_new_for_str_successfully() {
    let input  = &"foobar"[..];
    let output = StrSpan {
        offset : 0,
        line  : 1,
        fragment : input
    };

    assert_eq!(StrSpan::new(input), output);
}

#[test]
fn it_should_slice_for_str() {
    let str_slice = StrSpan::new("foobar");
    assert_eq!(str_slice.slice(1..), StrSpan {
        offset: 1,
        line: 1,
        fragment: "oobar"
    });
    assert_eq!(str_slice.slice(1..3), StrSpan {
        offset: 1,
        line: 1,
        fragment: "oo"
    });
    assert_eq!(str_slice.slice(..3), StrSpan {
        offset: 0,
        line: 1,
        fragment: "foo"
    });
    assert_eq!(str_slice.slice(..), str_slice);
}

#[test]
fn it_should_slice_for_u8() {
    let bytes_slice = BytesSpan::new(b"foobar");
    assert_eq!(bytes_slice.slice(1..), BytesSpan {
        offset: 1,
        line: 1,
        fragment: b"oobar"
    });
    assert_eq!(bytes_slice.slice(1..3), BytesSpan {
        offset: 1,
        line: 1,
        fragment: b"oo"
    });
    assert_eq!(bytes_slice.slice(..3), BytesSpan {
        offset: 0,
        line: 1,
        fragment: b"foo"
    });
    assert_eq!(bytes_slice.slice(..), bytes_slice);
}

#[test]
fn it_should_calculate_columns() {
    let input = StrSpan::new("foo
        bar");


    let bar_idx = input.find_substring("bar").unwrap();
    assert_eq!(input.slice(bar_idx..).get_column(), 9);
}

#[test]
fn it_should_calculate_columns_accurately_with_non_ascii_chars() {
    let s = StrSpan::new("メカジキ");
    assert_eq!(s.slice(6..).get_column_utf8(), Ok(3));
}

#[test]
#[should_panic(expected = "offset is too big")]
fn it_should_panic_when_getting_column_if_offset_is_too_big() {
    let s = StrSpan {
        offset: usize::max_value(),
        fragment: "",
        line: 1
    };
    s.get_column();
}

#[test]
fn it_should_iterate_indices() {
    let str_slice = StrSpan::new("foobar");
    assert_eq!(str_slice.iter_indices().collect::<Vec<(usize, char)>>(), vec![
        (0, 'f'), (1, 'o'), (2, 'o'),
        (3, 'b'), (4, 'a'), (5, 'r')
    ]);
    assert_eq!(StrSpan::new("").iter_indices().collect::<Vec<(usize, char)>>(),
        vec![]
    );
}

#[test]
fn it_should_iterate_elements() {
    let str_slice = StrSpan::new("foobar");
    assert_eq!(str_slice.iter_elements().collect::<Vec<char>>(), vec![
        'f', 'o', 'o', 'b', 'a', 'r'
    ]);
    assert_eq!(StrSpan::new("").iter_elements().collect::<Vec<char>>(),
        vec![]
    );
}

#[test]
fn it_should_position_char() {
    let str_slice = StrSpan::new("foobar");
    assert_eq!(str_slice.position(|x| x == 'a'), Some(4));
    assert_eq!(str_slice.position(|x| x == 'c'), None);
}

#[test]
fn it_should_compare_elements() {
    assert_eq!(StrSpan::new("foobar").compare("foo"), CompareResult::Ok);
    assert_eq!(StrSpan::new("foobar").compare("bar"), CompareResult::Error);
    assert_eq!(StrSpan::new("foobar").compare("foobar"), CompareResult::Ok);
    assert_eq!(StrSpan::new("foobar").compare_no_case("fooBar"), CompareResult::Ok);
    assert_eq!(StrSpan::new("foobar").compare("foobarbaz"),
       CompareResult::Incomplete);

    // FIXME: WTF! The line below doesn't compile unless we stop comparing
    // LocatedSpan<&[u8]> with &str
    //
    // assert_eq!(BytesSpan::new(b"foobar").compare(b"foo"), CompareResult::Ok);
    assert_eq!(BytesSpan::new(b"foobar").compare("foo"), CompareResult::Ok);
}

#[test]
fn it_should_find_token() {
    assert!('a'.find_token(StrSpan::new("foobar")));
    assert!(b'a'.find_token(StrSpan::new("foobar")));
    assert!(&(b'a').find_token(StrSpan::new("foobar")));
    assert!(!'c'.find_token(StrSpan::new("foobar")));
    assert!(!b'c'.find_token(StrSpan::new("foobar")));
    assert!(!(&b'c').find_token(StrSpan::new("foobar")));

    assert!(b'a'.find_token(BytesSpan::new(b"foobar")));
    assert!(&(b'a').find_token(BytesSpan::new(b"foobar")));
    assert!(!b'c'.find_token(BytesSpan::new(b"foobar")));
    assert!(!(&b'c').find_token(BytesSpan::new(b"foobar")));
}

#[test]
fn it_should_find_substring() {
    assert_eq!(StrSpan::new("foobar").find_substring("bar"), Some(3));
    assert_eq!(StrSpan::new("foobar").find_substring("baz"), None);
    assert_eq!(BytesSpan::new(b"foobar").find_substring("bar"), Some(3));
    assert_eq!(BytesSpan::new(b"foobar").find_substring("baz"), None);
}

#[test]
fn it_should_parse_to_string() {
    assert_eq!(StrSpan::new("foobar").parse_to(), Some("foobar".to_string()));
    assert_eq!(BytesSpan::new(b"foobar").parse_to(), Some("foobar".to_string()));
}


// https://github.com/Geal/nom/blob/eee82832fafdfdd0505546d224caa466f7d39a15/src/util.rs#L710-L720
#[test]
fn it_should_calculate_offset_for_u8() {
  let s = b"abcd123";
  let a = &s[..];
  let b = &a[2..];
  let c = &a[..4];
  let d = &a[3..5];
  assert_eq!(a.offset(b), 2);
  assert_eq!(a.offset(c), 0);
  assert_eq!(a.offset(d), 3);
}

// https://github.com/Geal/nom/blob/eee82832fafdfdd0505546d224caa466f7d39a15/src/util.rs#L722-L732
#[test]
fn it_should_calculate_offset_for_str() {
    let s = StrSpan::new("abcřèÂßÇd123");
    let a = s.slice(..);
    let b = a.slice(7..);
    let c = a.slice(..5);
    let d = a.slice(5..9);
    assert_eq!(a.offset(&b), 7);
    assert_eq!(a.offset(&c), 0);
    assert_eq!(a.offset(&d), 5);
}

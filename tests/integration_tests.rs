#[macro_use]
extern crate nom;
extern crate nom_locate;

use std::ops::Range;
use std::fmt::Debug;
use nom_locate::LocatedSpan;
use std::cmp;
use nom::{IResult, ErrorKind, FindSubstring, InputLength, Slice};

type StrSpan<'a> = LocatedSpan<&'a str>;
type BytesSpan<'a> = LocatedSpan<&'a [u8]>;

named!(simple_parser_str< StrSpan, Vec<StrSpan> >, do_parse!(
    foo: ws!(tag!("foo")) >>
    bar: ws!(tag!("bar")) >>
    baz: many0!(ws!(tag!("baz"))) >>
    eof: eof!() >>
    ({
        let mut res = vec![foo, bar];
        res.extend(baz);
        res.push(eof);
        res
    })
));

named!(simple_parser_u8< BytesSpan, Vec<BytesSpan> >, do_parse!(
    foo: ws!(tag!("foo")) >>
    bar: ws!(tag!("bar")) >>
    baz: many0!(ws!(tag!("baz"))) >>
    eof: eof!() >>
    ({
        let mut res = vec![foo, bar];
        res.extend(baz);
        res.push(eof);
        res
    })
));

struct Position {
    line: u32,
    column: u32,
    offset: usize,
    fragment_len: usize
}

fn test_str_fragments<'a, F, T>(parser: F, input: T, fragments: Vec<Position>)
    where F: Fn(LocatedSpan<T>) -> IResult<LocatedSpan<T>, Vec<LocatedSpan<T>>>,
          T: InputLength + Slice<Range<usize>> + Debug + PartialEq {

    let expected: Vec<LocatedSpan<T>> = fragments.iter().map(|pos: &Position| {
        LocatedSpan {
            column: pos.column,
            line: pos.line,
            offset: pos.offset,
            fragment: input.slice(pos.offset..cmp::min(pos.offset + pos.fragment_len, input.input_len()))
        }
    }).collect();
    let res = parser(LocatedSpan::new(input));
    assert!(res.is_done(), "the parser should run successfully");
    let (remaining, output) = res.unwrap();
    assert!(remaining.fragment.input_len() == 0, "no input should remain");
    assert_eq!(output, expected);
}

#[test]
fn it_locates_str_fragments() {
    test_str_fragments(simple_parser_str, "foobarbaz", vec![
        Position { line: 1, column: 0, offset: 0, fragment_len: 3 },
        Position { line: 1, column: 3, offset: 3, fragment_len: 3 },
        Position { line: 1, column: 6, offset: 6, fragment_len: 3 },
        Position { line: 1, column: 9, offset: 9, fragment_len: 3 }
    ]);
    test_str_fragments(simple_parser_str, " foo
        bar
            baz", vec![
        Position { line: 1, column: 1,  offset: 1,  fragment_len: 3 },
        Position { line: 2, column: 8,  offset: 13, fragment_len: 3 },
        Position { line: 3, column: 12, offset: 29, fragment_len: 3 },
        Position { line: 3, column: 15, offset: 32, fragment_len: 3 }
    ]);
}

#[test]
fn it_locates_u8_fragments() {
    test_str_fragments(simple_parser_u8, &b"foobarbaz"[..], vec![
        Position { line: 1, column: 0, offset: 0, fragment_len: 3 },
        Position { line: 1, column: 3, offset: 3, fragment_len: 3 },
        Position { line: 1, column: 6, offset: 6, fragment_len: 3 },
        Position { line: 1, column: 9, offset: 9, fragment_len: 3 }
    ]);
    test_str_fragments(simple_parser_u8, &b" foo
        bar
            baz"[..], vec![
        Position { line: 1, column: 1,  offset: 1,  fragment_len: 3 },
        Position { line: 2, column: 8,  offset: 13, fragment_len: 3 },
        Position { line: 3, column: 12, offset: 29, fragment_len: 3 },
        Position { line: 3, column: 15, offset: 32, fragment_len: 3 }
    ]);
}

fn find_substring<'a>(input: StrSpan<'a>, substr: &str) -> IResult< StrSpan<'a>, StrSpan<'a> > {
    let substr_len = substr.len();
    match input.find_substring(substr) {
        None => IResult::Error(error_position!(ErrorKind::Custom(1), input)),
        Some(pos) => IResult::Done(input.slice(pos+substr_len..), input.slice(pos..pos+substr_len))
    }
}

named!(plague<StrSpan, Vec<StrSpan> >, do_parse!(
    bacille: apply!(find_substring, "le bacille") >>
    bacille_pronouns: many0!(apply!(find_substring, "il ")) >>
    peste: apply!(find_substring, "la peste") >>
    take_until_and_consume1!(".") >>
    ({
        let mut res = vec![bacille];
        res.extend(bacille_pronouns);
        res.push(peste);
        res
    })
));


#[test]
fn it_locates_complex_fragments() {
    // Lorem ipsum is boring. Let's quote Camus' Plague.
    let input = "Écoutant, en effet, les cris d’allégresse qui montaient de la ville,
Rieux se souvenait que cette allégresse était toujours menacée.
Car il savait ce que cette foule en joie ignorait,
et qu’on peut lire dans les livres,
que le bacille de la peste ne meurt ni ne disparaît jamais,
qu’il peut rester pendant des dizaines d’années endormi dans
les meubles et le linge, qu’il attend patiemment dans les chambres, les caves,
les malles, les mouchoirs et les paperasses,
et que, peut-être, le jour viendrait où,
pour le malheur et l’enseignement des hommes,
la peste réveillerait ses rats et les enverrait mourir dans une cité heureuse.";

    let expected = vec![
        Position { line: 5,  column: 4,  offset: 233, fragment_len: 10 },
        Position { line: 6,  column: 3,  offset: 295, fragment_len: 3  },
        Position { line: 7,  column: 28, offset: 386, fragment_len: 3  },
        Position { line: 11, column: 0,  offset: 573, fragment_len: 8  }
    ];

    test_str_fragments(plague, input, expected);
}

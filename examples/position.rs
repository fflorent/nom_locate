extern crate nom;
extern crate nom_locate;

use nom::bytes::complete::{tag, take_until};
use nom::IResult;
use nom_locate::{position, LocatedSpan};

type Span<'a> = LocatedSpan<&'a str>;

struct Token<'a> {
    pub position: Span<'a>,
    pub _foo: &'a str,
    pub _bar: &'a str,
}

fn parse_foobar(s: Span) -> IResult<Span, Token> {
    let (s, _) = take_until("foo")(s)?;
    let (s, pos) = position(s)?;
    let (s, foo) = tag("foo")(s)?;
    let (s, bar) = tag("bar")(s)?;

    Ok((
        s,
        Token {
            position: pos,
            _foo: foo.fragment(),
            _bar: bar.fragment(),
        },
    ))
}

fn main() {
    let input = Span::new("Lorem ipsum \n foobar");
    let output = parse_foobar(input);
    let position = output.unwrap().1.position;
    assert_eq!(position, unsafe {
        Span::new_from_raw_offset(
            14, // offset
            2,  // line
            "", // fragment
            (), // extra
        )
    });
    assert_eq!(position.get_column(), 2);
}

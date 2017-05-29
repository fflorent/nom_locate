# nom_locate
A special input type for nom to locate tokens

## How to use it
````rust
#[macro_use]
extern crate nom;
extern crate nom_locate;

use nom_locate::LocatedSpan;
type Span<'a> = LocatedSpan<&'a str>;

struct Token<'a> {
    pub position: Span<'a>,
    pub foo: String,
    pub bar: String,
}

named!(parse_foobar( Span ) -> Token, do_parse!(
    take_until!("foo") >>
    position: tag!("") >> // Little trick to capture the position
    foo: tag!("foo") >>
    bar: tag!("bar") >>
    (Token {
        position: position,
        foo: foo.to_string(),
        bar: bar.to_string()
    })
));

fn main () {
    let input = Span::new("Lorem ipsum \n foobar");
    let output = parse_foobar(input);
    assert_eq!(output.unwrap().1.position, Span {
        offset: 14,
        column: 1,
        line: 2,
        fragment: ""
    });
}
````

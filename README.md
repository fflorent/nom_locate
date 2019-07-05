# nom_locate

[![Build Status](https://travis-ci.org/fflorent/nom_locate.svg?branch=master)](https://travis-ci.org/fflorent/nom_locate)
[![Coverage Status](https://coveralls.io/repos/github/fflorent/nom_locate/badge.svg?branch=master)](https://coveralls.io/github/fflorent/nom_locate?branch=master)
[![](https://img.shields.io/crates/v/nom_locate.svg)](https://crates.io/crates/nom_locate)

A special input type for [nom](https://github.com/geal/nom) to locate tokens

## Documentation

The documentation of the crate is available [here](https://docs.rs/nom_locate/).

## How to use it
The crate provide the [`LocatedSpan` struct](https://docs.rs/nom_locate/struct.LocatedSpan.html) that encapsulates the data. Look at the below example and the explanations:

````rust
#[macro_use]
extern crate nom;
#[macro_use]
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
    position: position!() >>
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
    let position = output.unwrap().1.position;
    assert_eq!(position, Span {
        offset: 14,
        line: 2,
        fragment: "",
        extra: (),
    });
    assert_eq!(position.get_column(), 2);
}
````

### Import

Import [nom](https://github.com/geal/nom) and nom_locate.

````rust
#[macro_use]
extern crate nom;
extern crate nom_locate;

use nom_locate::LocatedSpan;
````

Also you'd probably create [type alias](https://doc.rust-lang.org/book/type-aliases.html) for convenience so you don't have to specify the `fragment` type every time:

````rust
type Span<'a> = LocatedSpan<&'a str>;
````

### Define the output structure

The output structure of your parser may contain the position as a `Span` (which provides the `index`, `line` and `column` information to locate your token).

````rust
struct Token<'a> {
    pub position: Span<'a>,
    pub foo: String,
    pub bar: String,
}
````

### Create the parser

The parser has to accept a `Span` as an input. You may use `position!()` in your nom parser, in order to capture the location of your token:

````rust
named!(parse_foobar( Span ) -> Token, do_parse!(
    take_until!("foo") >>
    position: position!() >>
    foo: tag!("foo") >>
    bar: tag!("bar") >>
    (Token {
        position: position,
        foo: foo.to_string(),
        bar: bar.to_string()
    })
));
````

### Call the parser

The parser returns a `nom::IResult<Token, _>` (hence the `unwrap().1`). The `position` property contains the `offset`, `line` and `column`.

````rust
fn main () {
    let input = Span::new("Lorem ipsum \n foobar");
    let output = parse_foobar(input);
    let position = output.unwrap().1.position;
    assert_eq!(position, Span {
        offset: 14,
        line: 2,
        fragment: ""
    });
    assert_eq!(position.get_column(), 2);
}
````

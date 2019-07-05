#![feature(test)]
extern crate test;

use nom::Slice;
use nom_locate::LocatedSpan;

use test::Bencher;

// Lorem ipsum is boring. Let's quote Camus' Plague.
const TEXT: &str = "Écoutant, en effet, les cris d’allégresse qui montaient de la ville,
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

const TEXT_ASCII: &str = "Ecoutant, en effet, les cris d'allegresse qui montaient de la ville,
Rieux se souvenait que cette allegresse etait toujours menacee.
Car il savait ce que cette foule en joie ignorait,
et qu'on peut lire dans les livres,
que le bacille de la peste ne meurt ni ne disparait jamais,
qu'il peut rester pendant des dizaines d'annees endormi dans
les meubles et le linge, qu'il attend patiemment dans les chambres, les caves,
les malles, les mouchoirs et les paperasses,
et que, peut-etre, le jour viendrait ou,
pour le malheur et l'enseignement des hommes,
la peste reveillerait ses rats et les enverrait mourir dans une cite heureuse.";

#[bench]
fn bench_slice_full(b: &mut Bencher) {
    let input = LocatedSpan::new(TEXT);

    b.iter(|| {
        input.slice(..);
    });
}

#[bench]
fn bench_slice_from(b: &mut Bencher) {
    let input = LocatedSpan::new(TEXT);

    b.iter(|| {
        input.slice(200..);
    });
}

#[bench]
fn bench_slice_from_zero(b: &mut Bencher) {
    let input = LocatedSpan::new(TEXT);

    b.iter(|| {
        input.slice(0..);
    });
}

#[bench]
fn bench_slice_to(b: &mut Bencher) {
    let input = LocatedSpan::new(TEXT);

    b.iter(|| {
        input.slice(..200);
    });
}

#[bench]
fn bench_slice(b: &mut Bencher) {
    let input = LocatedSpan::new(TEXT);

    b.iter(|| {
        input.slice(200..300);
    });
}

#[bench]
fn bench_slice_columns_only(b: &mut Bencher) {
    let text = TEXT.replace("\n", "");
    let input = LocatedSpan::new(text.as_str());

    b.iter(|| {
        input.slice(500..501).get_utf8_column();
    });
}

#[bench]
fn bench_slice_columns_only_for_ascii_text(b: &mut Bencher) {
    #[allow(unused)]
    use std::ascii::AsciiExt;
    let text = TEXT_ASCII.replace("\n", "");
    let input = LocatedSpan::new(text.as_str());

    assert!(text.is_ascii());
    b.iter(|| {
        input.slice(500..501).get_column();
    });
}

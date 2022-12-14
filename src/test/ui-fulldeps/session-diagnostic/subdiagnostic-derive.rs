// check-fail
// Tests error conditions for specifying subdiagnostics using #[derive(Subdiagnostic)]

// The proc_macro2 crate handles spans differently when on beta/stable release rather than nightly,
// changing the output of this test. Since Subdiagnostic is strictly internal to the compiler
// the test is just ignored on stable and beta:
// ignore-beta
// ignore-stable

#![feature(rustc_private)]
#![crate_type = "lib"]

extern crate rustc_errors;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_macros;

use rustc_errors::Applicability;
use rustc_span::Span;
use rustc_macros::Subdiagnostic;

#[derive(Subdiagnostic)]
#[label(parser_add_paren)]
struct A {
    #[primary_span]
    span: Span,
    var: String,
}

#[derive(Subdiagnostic)]
enum B {
    #[label(parser_add_paren)]
    A {
        #[primary_span]
        span: Span,
        var: String,
    },
    #[label(parser_add_paren)]
    B {
        #[primary_span]
        span: Span,
        var: String,
    }
}

#[derive(Subdiagnostic)]
#[label(parser_add_paren)]
//~^ ERROR label without `#[primary_span]` field
struct C {
    var: String,
}

#[derive(Subdiagnostic)]
#[label]
//~^ ERROR diagnostic slug must be first argument
struct D {
    #[primary_span]
    span: Span,
    var: String,
}

#[derive(Subdiagnostic)]
#[foo]
//~^ ERROR `#[foo]` is not a valid attribute
//~^^ ERROR cannot find attribute `foo` in this scope
struct E {
    #[primary_span]
    span: Span,
    var: String,
}

#[derive(Subdiagnostic)]
#[label = "..."]
//~^ ERROR `#[label = ...]` is not a valid attribute
struct F {
    #[primary_span]
    span: Span,
    var: String,
}

#[derive(Subdiagnostic)]
#[label(bug = "...")]
//~^ ERROR `#[label(bug = ...)]` is not a valid attribute
//~| ERROR diagnostic slug must be first argument
struct G {
    #[primary_span]
    span: Span,
    var: String,
}

#[derive(Subdiagnostic)]
#[label("...")]
//~^ ERROR `#[label("...")]` is not a valid attribute
//~| ERROR diagnostic slug must be first argument
struct H {
    #[primary_span]
    span: Span,
    var: String,
}

#[derive(Subdiagnostic)]
#[label(slug = 4)]
//~^ ERROR `#[label(slug = ...)]` is not a valid attribute
//~| ERROR diagnostic slug must be first argument
struct J {
    #[primary_span]
    span: Span,
    var: String,
}

#[derive(Subdiagnostic)]
#[label(slug("..."))]
//~^ ERROR `#[label(slug(...))]` is not a valid attribute
//~| ERROR diagnostic slug must be first argument
struct K {
    #[primary_span]
    span: Span,
    var: String,
}

#[derive(Subdiagnostic)]
#[label(slug)]
//~^ ERROR cannot find value `slug` in module `rustc_errors::fluent`
//~^^ NOTE not found in `rustc_errors::fluent`
struct L {
    #[primary_span]
    span: Span,
    var: String,
}

#[derive(Subdiagnostic)]
#[label()]
//~^ ERROR diagnostic slug must be first argument of a `#[label(...)]` attribute
struct M {
    #[primary_span]
    span: Span,
    var: String,
}

#[derive(Subdiagnostic)]
#[label(parser_add_paren, code = "...")]
//~^ ERROR `#[label(code = ...)]` is not a valid attribute
struct N {
    #[primary_span]
    span: Span,
    var: String,
}

#[derive(Subdiagnostic)]
#[label(parser_add_paren, applicability = "machine-applicable")]
//~^ ERROR `#[label(applicability = ...)]` is not a valid attribute
struct O {
    #[primary_span]
    span: Span,
    var: String,
}

#[derive(Subdiagnostic)]
#[foo]
//~^ ERROR cannot find attribute `foo` in this scope
//~^^ ERROR unsupported type attribute for subdiagnostic enum
enum P {
    #[label(parser_add_paren)]
    A {
        #[primary_span]
        span: Span,
        var: String,
    }
}

#[derive(Subdiagnostic)]
enum Q {
    #[bar]
    //~^ ERROR `#[bar]` is not a valid attribute
    //~^^ ERROR cannot find attribute `bar` in this scope
    A {
        #[primary_span]
        span: Span,
        var: String,
    }
}

#[derive(Subdiagnostic)]
enum R {
    #[bar = "..."]
    //~^ ERROR `#[bar = ...]` is not a valid attribute
    //~^^ ERROR cannot find attribute `bar` in this scope
    A {
        #[primary_span]
        span: Span,
        var: String,
    }
}

#[derive(Subdiagnostic)]
enum S {
    #[bar = 4]
    //~^ ERROR `#[bar = ...]` is not a valid attribute
    //~^^ ERROR cannot find attribute `bar` in this scope
    A {
        #[primary_span]
        span: Span,
        var: String,
    }
}

#[derive(Subdiagnostic)]
enum T {
    #[bar("...")]
    //~^ ERROR `#[bar(...)]` is not a valid attribute
    //~^^ ERROR cannot find attribute `bar` in this scope
    A {
        #[primary_span]
        span: Span,
        var: String,
    }
}

#[derive(Subdiagnostic)]
enum U {
    #[label(code = "...")]
    //~^ ERROR diagnostic slug must be first argument of a `#[label(...)]` attribute
    //~| ERROR `#[label(code = ...)]` is not a valid attribute
    A {
        #[primary_span]
        span: Span,
        var: String,
    }
}

#[derive(Subdiagnostic)]
enum V {
    #[label(parser_add_paren)]
    A {
        #[primary_span]
        span: Span,
        var: String,
    },
    B {
        #[primary_span]
        span: Span,
        var: String,
    }
}

#[derive(Subdiagnostic)]
#[label(parser_add_paren)]
//~^ ERROR label without `#[primary_span]` field
struct W {
    #[primary_span]
    //~^ ERROR the `#[primary_span]` attribute can only be applied to fields of type `Span` or `MultiSpan`
    span: String,
}

#[derive(Subdiagnostic)]
#[label(parser_add_paren)]
struct X {
    #[primary_span]
    span: Span,
    #[applicability]
    //~^ ERROR `#[applicability]` is only valid on suggestions
    applicability: Applicability,
}

#[derive(Subdiagnostic)]
#[label(parser_add_paren)]
struct Y {
    #[primary_span]
    span: Span,
    #[bar]
    //~^ ERROR `#[bar]` is not a valid attribute
    //~^^ ERROR cannot find attribute `bar` in this scope
    bar: String,
}

#[derive(Subdiagnostic)]
#[label(parser_add_paren)]
struct Z {
    #[primary_span]
    span: Span,
    #[bar = "..."]
    //~^ ERROR `#[bar = ...]` is not a valid attribute
    //~^^ ERROR cannot find attribute `bar` in this scope
    bar: String,
}

#[derive(Subdiagnostic)]
#[label(parser_add_paren)]
struct AA {
    #[primary_span]
    span: Span,
    #[bar("...")]
    //~^ ERROR `#[bar(...)]` is not a valid attribute
    //~^^ ERROR cannot find attribute `bar` in this scope
    bar: String,
}

#[derive(Subdiagnostic)]
#[label(parser_add_paren)]
struct AB {
    #[primary_span]
    span: Span,
    #[skip_arg]
    z: Z
}

#[derive(Subdiagnostic)]
union AC {
//~^ ERROR unexpected unsupported untagged union
    span: u32,
    b: u64
}

#[derive(Subdiagnostic)]
#[label(parser_add_paren)]
#[label(parser_add_paren)]
struct AD {
    #[primary_span]
    span: Span,
}

#[derive(Subdiagnostic)]
#[label(parser_add_paren, parser_add_paren)]
//~^ ERROR `#[label(parser_add_paren)]` is not a valid attribute
struct AE {
    #[primary_span]
    span: Span,
}

#[derive(Subdiagnostic)]
#[label(parser_add_paren)]
struct AF {
    #[primary_span]
    //~^ NOTE previously specified here
    span_a: Span,
    #[primary_span]
    //~^ ERROR specified multiple times
    span_b: Span,
}

#[derive(Subdiagnostic)]
struct AG {
    //~^ ERROR subdiagnostic kind not specified
    #[primary_span]
    span: Span,
}

#[derive(Subdiagnostic)]
#[suggestion(parser_add_paren, code = "...")]
struct AH {
    #[primary_span]
    span: Span,
    #[applicability]
    applicability: Applicability,
    var: String,
}

#[derive(Subdiagnostic)]
enum AI {
    #[suggestion(parser_add_paren, code = "...")]
    A {
        #[primary_span]
        span: Span,
        #[applicability]
        applicability: Applicability,
        var: String,
    },
    #[suggestion(parser_add_paren, code = "...")]
    B {
        #[primary_span]
        span: Span,
        #[applicability]
        applicability: Applicability,
        var: String,
    }
}

#[derive(Subdiagnostic)]
#[suggestion(parser_add_paren, code = "...", code = "...")]
//~^ ERROR specified multiple times
//~^^ NOTE previously specified here
struct AJ {
    #[primary_span]
    span: Span,
    #[applicability]
    applicability: Applicability,
}

#[derive(Subdiagnostic)]
#[suggestion(parser_add_paren, code = "...")]
struct AK {
    #[primary_span]
    span: Span,
    #[applicability]
    //~^ NOTE previously specified here
    applicability_a: Applicability,
    #[applicability]
    //~^ ERROR specified multiple times
    applicability_b: Applicability,
}

#[derive(Subdiagnostic)]
#[suggestion(parser_add_paren, code = "...")]
struct AL {
    #[primary_span]
    span: Span,
    #[applicability]
    //~^ ERROR the `#[applicability]` attribute can only be applied to fields of type `Applicability`
    applicability: Span,
}

#[derive(Subdiagnostic)]
#[suggestion(parser_add_paren, code = "...")]
struct AM {
    #[primary_span]
    span: Span,
}

#[derive(Subdiagnostic)]
#[suggestion(parser_add_paren)]
//~^ ERROR suggestion without `code = "..."`
struct AN {
    #[primary_span]
    span: Span,
    #[applicability]
    applicability: Applicability,
}

#[derive(Subdiagnostic)]
#[suggestion(parser_add_paren, code ="...", applicability = "foo")]
//~^ ERROR invalid applicability
struct AO {
    #[primary_span]
    span: Span,
}

#[derive(Subdiagnostic)]
#[help(parser_add_paren)]
struct AP {
    var: String
}

#[derive(Subdiagnostic)]
#[note(parser_add_paren)]
struct AQ;

#[derive(Subdiagnostic)]
#[suggestion(parser_add_paren, code = "...")]
//~^ ERROR suggestion without `#[primary_span]` field
struct AR {
    var: String,
}

#[derive(Subdiagnostic)]
#[suggestion(parser_add_paren, code ="...", applicability = "machine-applicable")]
struct AS {
    #[primary_span]
    span: Span,
}

#[derive(Subdiagnostic)]
#[label]
//~^ ERROR unsupported type attribute for subdiagnostic enum
enum AT {
    #[label(parser_add_paren)]
    A {
        #[primary_span]
        span: Span,
        var: String,
    }
}

#[derive(Subdiagnostic)]
#[suggestion(parser_add_paren, code ="{var}", applicability = "machine-applicable")]
struct AU {
    #[primary_span]
    span: Span,
    var: String,
}

#[derive(Subdiagnostic)]
#[suggestion(parser_add_paren, code ="{var}", applicability = "machine-applicable")]
//~^ ERROR `var` doesn't refer to a field on this type
struct AV {
    #[primary_span]
    span: Span,
}

#[derive(Subdiagnostic)]
enum AW {
    #[suggestion(parser_add_paren, code ="{var}", applicability = "machine-applicable")]
    A {
        #[primary_span]
        span: Span,
        var: String,
    }
}

#[derive(Subdiagnostic)]
enum AX {
    #[suggestion(parser_add_paren, code ="{var}", applicability = "machine-applicable")]
//~^ ERROR `var` doesn't refer to a field on this type
    A {
        #[primary_span]
        span: Span,
    }
}

#[derive(Subdiagnostic)]
#[warning(parser_add_paren)]
struct AY {}

#[derive(Subdiagnostic)]
#[warning(parser_add_paren)]
struct AZ {
    #[primary_span]
    span: Span,
}

#[derive(Subdiagnostic)]
#[suggestion(parser_add_paren, code = "...")]
//~^ ERROR suggestion without `#[primary_span]` field
struct BA {
    #[suggestion_part]
    //~^ ERROR `#[suggestion_part]` is not a valid attribute
    span: Span,
    #[suggestion_part(code = "...")]
    //~^ ERROR `#[suggestion_part(...)]` is not a valid attribute
    span2: Span,
    #[applicability]
    applicability: Applicability,
    var: String,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren, code = "...", applicability = "machine-applicable")]
//~^ ERROR multipart suggestion without any `#[suggestion_part(...)]` fields
//~| ERROR `#[multipart_suggestion(code = ...)]` is not a valid attribute
struct BBa {
    var: String,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren, applicability = "machine-applicable")]
struct BBb {
    #[suggestion_part]
    //~^ ERROR `#[suggestion_part(...)]` attribute without `code = "..."`
    span1: Span,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren, applicability = "machine-applicable")]
struct BBc {
    #[suggestion_part()]
    //~^ ERROR `#[suggestion_part(...)]` attribute without `code = "..."`
    span1: Span,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren)]
//~^ ERROR multipart suggestion without any `#[suggestion_part(...)]` fields
struct BC {
    #[primary_span]
    //~^ ERROR `#[primary_span]` is not a valid attribute
    span: Span,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren)]
struct BD {
    #[suggestion_part]
    //~^ ERROR `#[suggestion_part(...)]` attribute without `code = "..."`
    span1: Span,
    #[suggestion_part()]
    //~^ ERROR `#[suggestion_part(...)]` attribute without `code = "..."`
    span2: Span,
    #[suggestion_part(foo = "bar")]
    //~^ ERROR `#[suggestion_part(foo = ...)]` is not a valid attribute
    span4: Span,
    #[suggestion_part(code = "...")]
    //~^ ERROR the `#[suggestion_part(...)]` attribute can only be applied to fields of type `Span` or `MultiSpan`
    s1: String,
    #[suggestion_part()]
    //~^ ERROR the `#[suggestion_part(...)]` attribute can only be applied to fields of type `Span` or `MultiSpan`
    s2: String,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren, applicability = "machine-applicable")]
struct BE {
    #[suggestion_part(code = "...", code = ",,,")]
    //~^ ERROR specified multiple times
    //~| NOTE previously specified here
    span: Span,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren, applicability = "machine-applicable")]
struct BF {
    #[suggestion_part(code = "(")]
    first: Span,
    #[suggestion_part(code = ")")]
    second: Span,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren)]
struct BG {
    #[applicability]
    appl: Applicability,
    #[suggestion_part(code = "(")]
    first: Span,
    #[suggestion_part(code = ")")]
    second: Span,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren, applicability = "machine-applicable")]
struct BH {
    #[applicability]
    //~^ ERROR `#[applicability]` has no effect
    appl: Applicability,
    #[suggestion_part(code = "(")]
    first: Span,
    #[suggestion_part(code = ")")]
    second: Span,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren, applicability = "machine-applicable")]
struct BI {
    #[suggestion_part(code = "")]
    spans: Vec<Span>,
}

#[derive(Subdiagnostic)]
#[label(parser_add_paren)]
struct BJ {
    #[primary_span]
    span: Span,
    r#type: String,
}

/// with a doc comment on the type..
#[derive(Subdiagnostic)]
#[label(parser_add_paren)]
struct BK {
    /// ..and the field
    #[primary_span]
    span: Span,
}

/// with a doc comment on the type..
#[derive(Subdiagnostic)]
enum BL {
    /// ..and the variant..
    #[label(parser_add_paren)]
    Foo {
        /// ..and the field
        #[primary_span]
        span: Span,
    }
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren)]
struct BM {
    #[suggestion_part(code("foo"))]
    //~^ ERROR expected exactly one string literal for `code = ...`
    span: Span,
    r#type: String,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren)]
struct BN {
    #[suggestion_part(code("foo", "bar"))]
    //~^ ERROR expected exactly one string literal for `code = ...`
    span: Span,
    r#type: String,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren)]
struct BO {
    #[suggestion_part(code(3))]
    //~^ ERROR expected exactly one string literal for `code = ...`
    span: Span,
    r#type: String,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren)]
struct BP {
    #[suggestion_part(code())]
    //~^ ERROR expected exactly one string literal for `code = ...`
    span: Span,
    r#type: String,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(parser_add_paren)]
struct BQ {
    #[suggestion_part(code = 3)]
    //~^ ERROR `code = "..."`/`code(...)` must contain only string literals
    span: Span,
    r#type: String,
}

#![warn(clippy::enum_variant_names)]
#![allow(non_camel_case_types, clippy::upper_case_acronyms)]

enum FakeCallType {
    CALL,
    CREATE,
}

enum FakeCallType2 {
    CALL,
    CREATELL,
}

enum Foo {
    cFoo,
    cBar,
    cBaz,
}

enum Fooo {
    cFoo, // no error, threshold is 3 variants by default
    cBar,
}

enum Food {
    FoodGood,
    FoodMiddle,
    FoodBad,
}

enum Stuff {
    StuffBad, // no error
}

enum BadCallType {
    CallTypeCall,
    CallTypeCreate,
    CallTypeDestroy,
}

enum TwoCallType {
    // no error
    CallTypeCall,
    CallTypeCreate,
}

enum Consts {
    ConstantInt,
    ConstantCake,
    ConstantLie,
}

enum Two {
    // no error here
    ConstantInt,
    ConstantInfer,
}

enum Something {
    CCall,
    CCreate,
    CCryogenize,
}

enum Seal {
    With,
    Without,
}

enum Seall {
    With,
    WithOut,
    Withbroken,
}

enum Sealll {
    With,
    WithOut,
}

enum Seallll {
    WithOutCake,
    WithOutTea,
    WithOut,
}

enum NonCaps {
    Prefix的,
    PrefixTea,
    PrefixCake,
}

pub enum PubSeall {
    WithOutCake,
    WithOutTea,
    WithOut,
}

#[allow(clippy::enum_variant_names)]
pub mod allowed {
    pub enum PubAllowed {
        SomeThis,
        SomeThat,
        SomeOtherWhat,
    }
}

// should not lint
enum Pat {
    Foo,
    Bar,
    Path,
}

// should not lint
enum N {
    Pos,
    Neg,
    Float,
}

// should not lint
enum Peek {
    Peek1,
    Peek2,
    Peek3,
}

// should not lint
pub enum NetworkLayer {
    Layer2,
    Layer3,
}

// should lint suggesting `IData`, not only `Data` (see #4639)
enum IDataRequest {
    PutIData(String),
    GetIData(String),
    DeleteUnpubIData(String),
}

enum HIDataRequest {
    PutHIData(String),
    GetHIData(String),
    DeleteUnpubHIData(String),
}

enum North {
    Normal,
    NoLeft,
    NoRight,
}

// #8324
enum Phase {
    PreLookup,
    Lookup,
    PostLookup,
}

mod issue9018 {
    enum DoLint {
        _TypeCreate,
        _TypeRead,
        _TypeUpdate,
        _TypeDestroy,
    }

    enum DoLintToo {
        _CreateType,
        _UpdateType,
        _DeleteType,
    }

    enum DoNotLint {
        _Foo,
        _Bar,
        _Baz,
    }
}

fn main() {}

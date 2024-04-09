# RuMono: Fuzz Driver Synthesis for Rust Generic APIs

## Introduction 

This is the repository of RuMono, a tool for synthesizing the fuzz drivers for Rust libraries with support for generic APIs. RuMono aims to automatically synthesize fuzz drivers for every API in your Rust library. RuMono can synthesize valid and comprehensive fuzz drivers by inferring suitable concrete types for generic APIs and synthesize every implementation for generic APIs. Thus, RuMono is capable of detecting inconspicuous bugs within specific monomorphic variants of a generic API. To this end, RuMono employs a two-stage approach, involving reachable monomorphic API search and similarity pruning.

## Warning

We are in the process of reformating code, and the present version may encounter build issues when you following the instructions below. We will finish the document and release the docker build environment as soon as possible.


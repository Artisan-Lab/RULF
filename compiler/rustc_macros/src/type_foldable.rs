use quote::quote;
use syn::parse_quote;

pub fn type_foldable_derive(mut s: synstructure::Structure<'_>) -> proc_macro2::TokenStream {
    if let syn::Data::Union(_) = s.ast().data {
        panic!("cannot derive on union")
    }

    if !s.ast().generics.lifetimes().any(|lt| lt.lifetime.ident == "tcx") {
        s.add_impl_generic(parse_quote! { 'tcx });
    }

    s.add_bounds(synstructure::AddBounds::Generics);
    s.bind_with(|_| synstructure::BindStyle::Move);
    let body_fold = s.each_variant(|vi| {
        let bindings = vi.bindings();
        vi.construct(|_, index| {
            let bind = &bindings[index];
            quote! {
                ::rustc_middle::ty::fold::TypeFoldable::try_fold_with(#bind, __folder)?
            }
        })
    });

    s.bound_impl(
        quote!(::rustc_middle::ty::fold::TypeFoldable<'tcx>),
        quote! {
            fn try_fold_with<__F: ::rustc_middle::ty::fold::FallibleTypeFolder<'tcx>>(
                self,
                __folder: &mut __F
            ) -> Result<Self, __F::Error> {
                Ok(match self { #body_fold })
            }
        },
    )
}

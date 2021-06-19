use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::{parse_macro_input, FnArg, Ident, ItemFn, Signature};

#[proc_macro_attribute]
pub fn command(_metadata: TokenStream, input: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(input as ItemFn);

    // We want to wrap the function so we can reset the state of the ERCP driver
    // after its execution, regardless its result.

    // Let’s rename the wrapped function.
    let wrapped_sig = Signature {
        ident: Ident::new(
            &format!("__wrapped_{}", input_fn.sig.ident),
            Span::call_site(),
        ),
        ..input_fn.sig.clone()
    };

    // The wrapper gets the original name.
    let wrapper_sig = input_fn.sig;
    let attrs = input_fn.attrs;
    let vis = input_fn.vis;
    let block = input_fn.block;

    // Get the idents of the parameters so we can call the function.
    let params: Vec<_> = wrapped_sig
        .inputs
        .iter()
        .filter_map(|arg| {
            match arg {
                // We only want the typed arguments.
                FnArg::Typed(arg) => Some(arg.pat.clone()),
                _ => None,
            }
        })
        .collect();

    let wrapped = &wrapped_sig.ident;

    let quoted = quote! {
        #(#attrs)*
        #vis #wrapper_sig {
            let result = self.#wrapped(#(#params),*);
            // TODO: Make it work when ercp is not self.
            self.reset_state();
            result
        }

        #wrapped_sig #block
    };

    quoted.into()
}

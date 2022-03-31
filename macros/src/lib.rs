// Copyright 2021 Jean-Philippe Cugnet
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::{parse_macro_input, FnArg, Ident, ItemFn, Signature};

#[proc_macro_attribute]
pub fn command(metadata: TokenStream, input: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(input as ItemFn);

    let ercp = if metadata.is_empty() {
        quote! { self.ercp }
    } else {
        // IDEA: Check the value and provide a useful error.
        metadata.into()
    };

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
            #ercp.reset_state();
            result
        }

        #wrapped_sig #block
    };

    quoted.into()
}

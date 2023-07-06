use crate::clean::ItemKind;
use crate::clean::{self};
use crate::config::RenderOptions;
use crate::error::Error;
use crate::formats::cache::Cache;
use crate::formats::renderer;
use crate::fuzz_target::api_graph::ApiGraph;
use crate::fuzz_target::api_util;
use crate::fuzz_target::file_util;
use crate::fuzz_target::generic_function::GenericFunction;
use crate::fuzz_target::impl_util::{self, FullNameMap};
use crate::fuzz_target::{api_function, statistic};
use crate::html::format::join_with_double_colon;
use crate::TyCtxt;
use rustc_span::symbol::Symbol;
use std::cell::RefCell;
use std::rc::Rc;

pub(crate) struct FuzzTargetContext<'tcx> {
    pub cache: Cache,
    pub tcx: TyCtxt<'tcx>,
}

#[derive(Clone)]
pub struct FuzzTargetRenderer<'tcx> {
    context: Rc<FuzzTargetContext<'tcx>>,
    /// Current hierarchy of components leading down to what's currently being
    /// rendered
    current: Vec<Symbol>,
    api_dependency_graph: Rc<RefCell<ApiGraph<'tcx>>>,
    full_name_map: Rc<RefCell<FullNameMap>>,
}

impl<'tcx> FuzzTargetRenderer<'tcx> {
    fn analyse_item(&mut self, item: clean::Item) -> Result<(), Error> {
        let mut full_name: String =
            join_with_double_colon(&self.current) + "::" + item.name.unwrap().as_str();

        match *item.kind {
            ItemKind::FunctionItem(ref func) => {
                //println!("func = {:?}", func);
                statistic::inc("FUNCTIONS");
                if (!func.generics.is_empty()) {
                    statistic::inc("GENERIC_FUNCTIONS");
                }
                println!("Fn {}", full_name);
                let decl = func.decl.clone();
                let clean::FnDecl { inputs, output, .. } = decl;
                let inputs = api_util::extract_input_types(&inputs);
                let output = api_util::extract_output_type(&output);

                let api_unsafety = api_function::ApiUnsafety::_get_unsafety_from_fnheader(
                    &item.fn_header(self.context.tcx).unwrap(),
                );
                let api_fun = api_function::ApiFunction {
                    full_name,
                    inputs,
                    output,
                    _trait_full_path: None,
                    _unsafe_tag: api_unsafety,
                    mono: false,
                };
                if !func.generics.is_empty() {
                    let mut api_fun = GenericFunction::from(api_fun);
                    api_fun.add_generics(&func.generics);
                    self.api_dependency_graph.borrow_mut().generic_functions.push(api_fun);
                } else {
                    self.api_dependency_graph.borrow_mut().add_api_function(api_fun);
                }
            }
            ItemKind::MethodItem(_, _) => {
                unreachable!();
            }
            _ => {}
        }
        Ok(())
    }
}

impl<'tcx> renderer::FormatRenderer<'tcx> for FuzzTargetRenderer<'tcx> {
    fn descr() -> &'static str {
        "Fuzz Target Renderer"
    }

    const RUN_ON_MODULE: bool = true;

    fn init(
        krate: clean::Crate,
        _options: RenderOptions,
        cache: Cache,
        tcx: TyCtxt<'tcx>,
    ) -> Result<(Self, clean::Crate), Error> {
        println!("Fuzz Target Renderer Init");
        println!("crate: {}", krate.module.name.unwrap().as_str());
        let rcx = Rc::new(FuzzTargetContext { cache, tcx });
        let mut api_dependency_graph = ApiGraph::new(krate.name(tcx).to_string(), rcx.clone());
        //从cache中提出def_id与full_name的对应关系，存入full_name_map来进行调用
        //同时提取impl块中的内容，存入api_dependency_graph
        let mut full_name_map = FullNameMap::new();
        impl_util::extract_impls_from_cache(&mut full_name_map, &mut api_dependency_graph);
        //api_dependency_graph.print_impl_traits();
        /*         println!("==== full name map ====");
        println!("len: {:?}", full_name_map.map.len());
        println!("{:?}", full_name_map);
        println!("==== full name map end ===="); */

        Ok((
            FuzzTargetRenderer {
                context: rcx,
                current: Vec::new(),
                api_dependency_graph: Rc::new(RefCell::new(api_dependency_graph)),
                full_name_map: Rc::new(RefCell::new(full_name_map)),
            },
            krate,
        ))
    }
    /// Make a new renderer to render a child of the item currently being rendered.
    fn make_child_renderer(&self) -> Self {
        //println!("make child renderer");
        self.clone()
    }

    /// Renders a single non-module item. This means no recursive sub-item rendering is required.
    fn item(&mut self, item: clean::Item) -> Result<(), Error> {
        /*         println!("==== item ====");
        let mut debug_str = String::new();
        debug_str.push_str("\nname: ");
        if let Some(name) = item.name {
            debug_str.push_str(name.as_str());
        }
        debug_str.push_str(&format!("\n vis: {:?}", item.visibility));
        debug_str.push_str(&format!("\n item kind: {:?}", item.kind));
        println!("{}", debug_str); */
        self.analyse_item(item)
    }

    /// Renders a module (should not handle recursing into children).
    fn mod_item_in(&mut self, item: &clean::Item) -> Result<(), Error> {
        self.current.push(item.name.unwrap());
        self.api_dependency_graph
            .borrow_mut()
            .add_mod_visibility(&join_with_double_colon(&self.current), &item.visibility);

        /*         println!("==== mod_item_in ====");
               let mut debug_str = String::new();
               debug_str.push_str("\nname: ");
               if let Some(name) = item.name {
                   debug_str.push_str(name.as_str());
               }
               debug_str.push_str(&format!("\n vis: {:?}", item.visibility));
               debug_str.push_str(&format!("\n item kind: {:?}", item.kind));
               println!("{}", debug_str);

        */
        Ok(())
    }

    /// Runs after recursively rendering all sub-items of a module.
    fn mod_item_out(&mut self) -> Result<(), Error> {
        self.current.pop();
        Ok(())
    }

    /// Post processing hook for cleanup and dumping output to files.
    fn after_krate(&mut self) -> Result<(), Error> {
        println!("==== run after krate ====");
        let mut api_dependency_graph = self.api_dependency_graph.borrow_mut();
        
        api_dependency_graph.print_type_map();
        api_dependency_graph.print_type_trait_impls();
        api_dependency_graph.resolve_generic_functions();
        statistic::print_summary();
        //根据mod可见性和预包含类型过滤function
        api_dependency_graph.filter_functions();
        //寻找所有依赖，并且构建序列
        api_dependency_graph.find_all_dependencies();
        // api_dependency_graph._print_pretty_dependencies();

        let random_strategy = false;
        if !random_strategy {
            api_dependency_graph.default_generate_sequences();
        } else {
            use crate::fuzz_target::api_graph::GraphTraverseAlgorithm::_RandomWalk;
            api_dependency_graph.generate_all_possoble_sequences(_RandomWalk);
        }
        //api_dependency_graph._print_generated_libfuzzer_file();
        //api_dependency_graph._print_pretty_functions(false);
        //api_dependency_graph._print_generated_test_functions();
        // print some information
        use crate::fuzz_target::print_message;
        println!("total functions in crate : {:?}", api_dependency_graph.api_functions.len());
        print_message::_print_pretty_functions(&api_dependency_graph, &self.context.cache, false);
        println!(
            "total generic functions in crate : {:?}",
            api_dependency_graph.generic_functions.len()
        );
        //print_message::_print_pretty_sequences(&api_dependency_graph);
        //print_message::_print_pretty_functions(&api_dependency_graph, true);
        // print_message::_print_generated_afl_file(&api_dependency_graph);

        //println!("total test sequences : {:?}", api_dependency_graph.api_sequences.len());
        //use crate::html::afl_util;
        //afl_util::_AflHelpers::_print_all();
        if file_util::can_write_to_file(&api_dependency_graph._crate_name, random_strategy) {
            //whether to use random strategy
            let file_helper = file_util::FileHelper::new(&api_dependency_graph, random_strategy);
            // println!("file_helper:{:?}", file_helper);
            file_helper.write_files();
            if file_util::can_generate_libfuzzer_target(&api_dependency_graph._crate_name) {
                // println!("libfuzzer file_helper:{:?}", file_helper);
                file_helper.write_libfuzzer_files();
            }
        }

        Ok(())
    }

    fn cache(&self) -> &Cache {
        &self.context.cache
    }
}

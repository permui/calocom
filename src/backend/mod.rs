use crate::ast;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::StructType;
struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
}

impl<'ctx> CodeGen<'ctx> {
    fn new(name: &'ctx str, context: &'ctx Context) -> Self {
        let module = context.create_module(name);
        let builder = context.create_builder();
        CodeGen {
            context,
            module,
            builder,
        }
    }

    fn convert_type_to_llvm_type(&self, typ: &ast::Type) -> StructType {
        match typ {
            ast::Type::Unit => {
                // unit type should not be used for code generation
                unreachable!()
            }
            ast::Type::Arrow(a, b) => {
                todo!()
            }
            ast::Type::Tuple(l) => {
                todo!()
            }
            ast::Type::Enum(a) => {
                todo!()
            }
            ast::Type::Named(a) => {
                todo!()
            }
        }
    }
}

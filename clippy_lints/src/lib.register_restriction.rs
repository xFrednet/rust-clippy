// This file was generated by `cargo dev update_lints`.
// Use that command to update this file and do not edit by hand.
// Manual edits will be overwritten.

store.register_group(true, "clippy::restriction", Some("clippy_restriction"), [
    Some(LintId::of(arithmetic::FLOAT_ARITHMETIC)),
    Some(LintId::of(arithmetic::INTEGER_ARITHMETIC)),
    Some(LintId::of(as_conversions::AS_CONVERSIONS)),
    Some(LintId::of(asm_syntax::INLINE_ASM_X86_ATT_SYNTAX)),
    Some(LintId::of(asm_syntax::INLINE_ASM_X86_INTEL_SYNTAX)),
    Some(LintId::of(casts::FN_TO_NUMERIC_CAST_ANY)),
    Some(LintId::of(create_dir::CREATE_DIR)),
    Some(LintId::of(dbg_macro::DBG_MACRO)),
    Some(LintId::of(default_numeric_fallback::DEFAULT_NUMERIC_FALLBACK)),
    Some(LintId::of(default_union_representation::DEFAULT_UNION_REPRESENTATION)),
    Some(LintId::of(disallowed_script_idents::DISALLOWED_SCRIPT_IDENTS)),
    Some(LintId::of(else_if_without_else::ELSE_IF_WITHOUT_ELSE)),
    Some(LintId::of(exhaustive_items::EXHAUSTIVE_ENUMS)),
    Some(LintId::of(exhaustive_items::EXHAUSTIVE_STRUCTS)),
    Some(LintId::of(exit::EXIT)),
    Some(LintId::of(float_literal::LOSSY_FLOAT_LITERAL)),
    Some(LintId::of(if_then_some_else_none::IF_THEN_SOME_ELSE_NONE)),
    Some(LintId::of(implicit_return::IMPLICIT_RETURN)),
    Some(LintId::of(indexing_slicing::INDEXING_SLICING)),
    Some(LintId::of(inherent_impl::MULTIPLE_INHERENT_IMPL)),
    Some(LintId::of(integer_division::INTEGER_DIVISION)),
    Some(LintId::of(let_underscore::LET_UNDERSCORE_MUST_USE)),
    Some(LintId::of(literal_representation::DECIMAL_LITERAL_REPRESENTATION)),
    Some(LintId::of(map_err_ignore::MAP_ERR_IGNORE)),
    Some(LintId::of(matches::REST_PAT_IN_FULLY_BOUND_STRUCTS)),
    Some(LintId::of(matches::WILDCARD_ENUM_MATCH_ARM)),
    Some(LintId::of(mem_forget::MEM_FORGET)),
    Some(LintId::of(methods::CLONE_ON_REF_PTR)),
    Some(LintId::of(methods::EXPECT_USED)),
    Some(LintId::of(methods::FILETYPE_IS_FILE)),
    Some(LintId::of(methods::GET_UNWRAP)),
    Some(LintId::of(methods::UNWRAP_USED)),
    Some(LintId::of(misc::FLOAT_CMP_CONST)),
    Some(LintId::of(misc_early::SEPARATED_LITERAL_SUFFIX)),
    Some(LintId::of(misc_early::UNNEEDED_FIELD_PATTERN)),
    Some(LintId::of(misc_early::UNSEPARATED_LITERAL_SUFFIX)),
    Some(LintId::of(missing_doc::MISSING_DOCS_IN_PRIVATE_ITEMS)),
    Some(LintId::of(missing_enforced_import_rename::MISSING_ENFORCED_IMPORT_RENAMES)),
    Some(LintId::of(missing_inline::MISSING_INLINE_IN_PUBLIC_ITEMS)),
    Some(LintId::of(module_style::MOD_MODULE_FILES)),
    Some(LintId::of(module_style::SELF_NAMED_MODULE_FILES)),
    Some(LintId::of(modulo_arithmetic::MODULO_ARITHMETIC)),
    Some(LintId::of(panic_in_result_fn::PANIC_IN_RESULT_FN)),
    Some(LintId::of(panic_unimplemented::PANIC)),
    Some(LintId::of(panic_unimplemented::TODO)),
    Some(LintId::of(panic_unimplemented::UNIMPLEMENTED)),
    Some(LintId::of(panic_unimplemented::UNREACHABLE)),
    Some(LintId::of(pattern_type_mismatch::PATTERN_TYPE_MISMATCH)),
    Some(LintId::of(same_name_method::SAME_NAME_METHOD)),
    Some(LintId::of(shadow::SHADOW_REUSE)),
    Some(LintId::of(shadow::SHADOW_SAME)),
    Some(LintId::of(shadow::SHADOW_UNRELATED)),
    Some(LintId::of(single_char_lifetime_names::SINGLE_CHAR_LIFETIME_NAMES)),
    Some(LintId::of(strings::STRING_ADD)),
    Some(LintId::of(strings::STRING_SLICE)),
    Some(LintId::of(strings::STRING_TO_STRING)),
    Some(LintId::of(strings::STR_TO_STRING)),
    Some(LintId::of(types::RC_BUFFER)),
    Some(LintId::of(types::RC_MUTEX)),
    Some(LintId::of(undocumented_unsafe_blocks::UNDOCUMENTED_UNSAFE_BLOCKS)),
    Some(LintId::of(unicode::NON_ASCII_LITERAL)),
    Some(LintId::of(unnecessary_self_imports::UNNECESSARY_SELF_IMPORTS)),
    Some(LintId::of(unwrap_in_result::UNWRAP_IN_RESULT)),
    Some(LintId::of(verbose_file_reads::VERBOSE_FILE_READS)),
    Some(LintId::of(write::PRINT_STDERR)),
    Some(LintId::of(write::PRINT_STDOUT)),
    Some(LintId::of(write::USE_DEBUG)),
].iter().copied().flatten().collect::<Vec<_>>())

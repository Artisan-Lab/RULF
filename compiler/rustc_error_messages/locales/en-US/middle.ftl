middle_drop_check_overflow =
    overflow while adding drop-check rules for {$ty}
    .note = overflowed on {$overflow_ty}

middle_opaque_hidden_type_mismatch =
    concrete type differs from previous defining opaque type use
    .label = expected `{$self_ty}`, got `{$other_ty}`

middle_conflict_types =
    this expression supplies two conflicting concrete types for the same opaque type

middle_previous_use_here =
    previous use here

middle_limit_invalid =
    `limit` must be a non-negative integer
    .label = {$error_str}

middle_const_eval_non_int =
    constant evaluation of enum discriminant resulted in non-integer

middle_unknown_layout =
    the type `{$ty}` has an unknown layout

middle_values_too_big =
    values of the type `{$ty}` are too big for the current architecture

middle_cannot_be_normalized =
    unable to determine layout for `{$ty}` because `{$failure_ty}` cannot be normalized


module Libraries__ModField {

newtype modulo = x : nat | 0 < x witness 1

datatype ModField = ModField(
    val: int,
    mod: modulo
)

/* Evaluates to true iff m and n are members of the same field */
predicate members_of_same_field(m: ModField, n: ModField) {
    m.mod == n.mod  
}

/* Maps m to its canonical representation */
function canonical(m: ModField) : ModField {
    ModField(m.val % m.mod as nat, m.mod)
}

/* Evaluates to true iff m and n are conguent */
predicate congruent(m: ModField, n: ModField) {
    members_of_same_field(m, n)
    && canonical(m) == canonical(n)
}

/* Maps to the sum of m and n */
function add(m: ModField, n: ModField) : ModField 
    requires members_of_same_field(m, n);
{
    assert m.mod == n.mod;
    ModField(m.val + n.val, m.mod)
}

/* Maps to the additive inverse of m */
function additiveInverse(m: ModField) : ModField 
{
    ModField(-m.val, m.mod)
}
} 

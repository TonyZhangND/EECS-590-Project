
module Libraries__Math {

lemma lemma_div(m:nat, k:nat) 
    requires m >= k;
    requires k >= 1;
    ensures m/k >= 1;
{
    if m == k {
        assert m / k == 1;
    }
}

} 

include "../Libraries/math.dfy"


module RS_def_i {
import opened Libraries__Math


function int_to_bit_seq(data: nat): seq<nat> 
    requires data >= 0;
    decreases data;
{
    if data == 0 then [] else 
    int_to_bit_seq(data/2) + [data %2]
}

function size(data: nat): nat
    decreases data;
{
    if data == 0 then 0 else 
    size(data/2) + 1
}


function power2(e:nat):nat
    decreases e;
{
   if (e==0) then 1 else 2 * power2(e-1)
}

function bit_seq_to_int(bits: seq<nat>): nat 
    requires forall i :: 0 <= i <|bits| ==> bits[i] == 0 || bits[i] == 1;
{
    bit_seq_to_int_helper(bits, 0)
}


function bit_seq_to_int_helper(bits: seq<nat>, i: nat): nat 
    requires forall k :: 0 <= k <|bits| ==> bits[k] == 0 || bits[k] == 1;
    decreases |bits|, i;
{   
    var len := |bits|;
    if len == 0 then 
        0 
    else 
        var trailing_bit := bits[len-1];
        bit_seq_to_int_helper(bits[..len-1], i+1) + trailing_bit * power2(i)
}

function divide(data: nat, k: nat): seq<nat> 
    requires k >= 1;
    requires size(data) % k == 0;
    requires size(data) >= k;
{
    var m := size(data);
    var t := m/k;  // t is size of each data chunk
    lemma_div(m, k);
    assert t >= 1;
    var bits := int_to_bit_seq(data);
    assert forall i :: 0 <= i <|bits| ==> bits[i] == 0 || bits[i] == 1;
    divide_helper(bits, t)
}

function divide_helper(bits: seq<nat>, t: nat): seq<nat> 
    requires t >= 1;
    requires forall k :: 0 <= k <|bits| ==> bits[k] == 0 || bits[k] == 1;
    decreases bits, t;
{
    if |bits| <= t then [bit_seq_to_int(bits)] else
    [bit_seq_to_int(bits[..t])] + divide_helper(bits[t..], t)
}

function encode(data: nat, h: nat, k: nat): seq<nat>
    requires h >= k >= 1;
    requires data >= 0;
{
    []
}
}
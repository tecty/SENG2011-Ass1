method Skippy(limit: nat)
{
    var skip := 7;
    var index := 0;
    while index<=limit
        invariant index % 7 == 0 && 0 <= index <= (limit/7 + 1) * 7;
        decreases  limit - index
    { index := index+skip; }
    assert index % 7 == 0 && index == (limit/7 + 1) * 7 ;
}
predicate unforgivenEqual(a:array<int>)
reads a
{ if (a.Length>=2) then (a[0]==a[1]) else false }
predicate forgivenEqual(a:array<int>)
reads a
{ (a.Length>=2) ==> a[0]==a[1] }

predicate forbiddenEqual(a:array<int>)
requires a.Length>=2
reads a
{ a[0]==a[1] }
method Main()
{
var a := new int[1]; // this is a ‘bad’ data: array is too short
var b := new int[2]; // this is ‘good’ data, but elements are unequal
a[0] := 1;
// assert forbiddenEqual(a); // always an assertion violation as a.Length==1
assert forgivenEqual(a); // a.Length==1 is 'caught’, predicate returns true
assert !unforgivenEqual(a); // a.Length==1 is 'caught’, predicate returns false
b[0], b[1] := 1, 2;
assert !forbiddenEqual(b); // all predicates return false
assert !forgivenEqual(b);
assert !unforgivenEqual(b);
}
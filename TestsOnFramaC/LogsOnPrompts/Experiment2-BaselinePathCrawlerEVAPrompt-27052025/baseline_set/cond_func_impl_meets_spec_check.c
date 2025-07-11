/*
Reasoning for annotations:
- `f` modifies x based on conditions and returns a derived value.
- `spec_f` models expected behavior, suitable for specification comparison.
- `cross_f` checks consistency between the two.
*/

/*@
 @ assigns \nothing;
 @ ensures \result == ((x < 0 ? (x + 1) : x) != 1 ? 2 * (x < 0 ? (x + 1) : x) : (x < 0 ? (x + 1) : x));
*/
int f(int x){ 
  if(x < 0)           // line 2
    x = x + 1; 
  if(x != 1)          // line 4
    x = 2*x; 
  return x; 
} 

/*@
 @ assigns \nothing;
 @ ensures \result == (x < 1 ? 2 * (x + 1) : 2 * x);
*/
int spec_f(int x){ 
  if(x < 1)           // line 10
    x = 2*(x + 1); 
  else 
    x = 2*x; 
  return x; 
} 

/*@
 @ assigns \nothing;
 @ ensures \result == ((f(x) == spec_f(x)) ? 1 : 0);
*/
int cross_f(int x){
  int imp = f(x);
  int spec = spec_f(x);
  if(imp != spec)     // line 20
    return 0; 
  else return 1;
}

/*@
  requires \true;
  assigns \nothing;

  behavior NotTriangle_Negative:
    assumes i < 0.0 || j < 0.0 || k < 0.0;
    ensures \result == 3;

  behavior NotTriangle_Inequality:
    assumes i >= 0.0 && j >= 0.0 && k >= 0.0 &&
            (i + j <= k || j + k <= i || k + i <= j);
    ensures \result == 3;

  behavior Equilateral:
    assumes i >= 0.0 && j >= 0.0 && k >= 0.0 &&
            i + j > k && j + k > i && k + i > j &&
            i == j && j == k;
    ensures \result == 2;

  behavior Isosceles:
    assumes i >= 0.0 && j >= 0.0 && k >= 0.0 &&
            i + j > k && j + k > i && k + i > j &&
            ((i == j && i != k) ||
             (i == k && i != j) ||
             (j == k && j != i));
    ensures \result == 1;

  behavior Scalene:
    assumes i >= 0.0 && j >= 0.0 && k >= 0.0 &&
            i + j > k && j + k > i && k + i > j &&
            i != j && j != k && i != k;
    ensures \result == 0;

  complete behaviors;
  disjoint behaviors;
*/
int Tritype(double i, double j, double k){
  int trityp = 0;
  if (i < 0.0 || j < 0.0 || k < 0.0)          // line 10  
    return 3;
  if (i + j <= k || j + k <= i || k + i <= j) // line 12 
    return 3;    
  if (i == j) trityp = trityp + 1;            // line 14
  if (i == k) trityp = trityp + 1;            // line 15
  if (j == k) trityp = trityp + 1;            // line 16
  if (trityp >= 2)                            // line 17
      trityp = 2;
  return trityp;
}


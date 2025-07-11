/*@ requires from <= cut <= to;
  @ ensures occ_a(e,t,from,to) == occ_a(e,t,from,cut)+occ_a(e,t,cut,to); 
  @ assigns \nothing; */
void occ_a_split(int e, char * t, int from, int cut, int to)
{
  /*@ loop invariant cut<=i<=to;
    @ loop invariant occ_a(e,t,from,i) == occ_a(e,t,from,cut)+occ_a(e,t,cut,i);
    @ loop assigns i;
    @ loop variant to - i; */
  for(int i = cut; i<to; i++);
}

#define same_elems_means_same_occ(_L1, _L2, _value, _array, _from, _to)	\
  /@									\
    loop invariant _from <= _k <= _to ;					\
    loop invariant occ_a{_L1}(_value, _array, _from, _k) ==		\
                   occ_a{_L2}(_value, _array, _from, _k) ; 		\
    loop assigns _k ;							\
    loop variant _to - _k ;						\
  @/									\
  for(int _k = _from ; _k < _to ; ++ _k) ;				\
  /@ assert occ_a{_L1}(_value, _array, _from, _to) ==			\
            occ_a{_L2}(_value, _array, _from, _to) ;			\
  @/

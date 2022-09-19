void is_positive(int * a, int size, int * r)
{
  int i;
  *r = 1;
  /*@ loop invariant 0 <= i <= size;
    @ loop invariant *r == 1 <==> \forall integer k; 0 <= k <i ==> 0 <= a[k];
    @ loop assigns i, *r;
    @ loop variant size - i; */
  for(i = 0; i < size; i++)
    if (a[i] < 0)
      *r = 0;
}

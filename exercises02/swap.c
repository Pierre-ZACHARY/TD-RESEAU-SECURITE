
/*@ requires \valid(a) && \valid(b);
  @ ensures \old(*a) == *b;
  @ ensures \old(*b) == *a;
  @ assigns *a,*b;
 */
void swap(int * a, int * b)
{
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

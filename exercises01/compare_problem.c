/*@ ensures (a < b  && \result == -1) || 
            (a == b && \result ==  0) || 
            (a > b  && \result ==  1); */
int compare(int a, int b)
{
  int tmp;
  if (a < b) tmp = - 1;
  if (a > b) tmp = 1;
  return tmp;
}

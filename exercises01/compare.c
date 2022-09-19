
/*@ ensures a < b ==> \result == -1;
    ensures a == b ==> \result == 0;
    ensures a > b ==> \result == 1;
    assigns \nothing;
 */
int compare(int a, int b)
{
  int tmp = 0;
  if (a < b) tmp = - 1;
  if (a > b) tmp = 1;
  return tmp;
}

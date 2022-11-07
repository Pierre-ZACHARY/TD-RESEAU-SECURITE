/* Pierre ZACHARY 2183251 */
#include <limits.h>
#include <stddef.h>
#include <stdbool.h>
#include <stddef.h>

/* FEUILLE 1 */

/* Exercice 4 */
/* INT_MIN <= x <= INT_MAX : Cette précondition implique que x ne peut pas être incrémenter ou décrémenter à l'intérieur de la fonction car on dépasserai potentiellement les bornes inférieurs ou supérieurs possibles pour un INT */
/* INT_MIN < x <= INT_MAX : La différence ici est que l'on peut décrémenter x car x ne peut pas être la borne inférieur possible ( INT_MIN ) et donc il existe y tel que INT_MIN<=y<x */
/* x > INT_MAX : Cette précondition est valide, cependant x ne sera pas exploitable, car son écriture binaire dépassera les 4 bytes */

/* Exercice 5 */
/*@ requires 0<= start + end <= INT_MAX;
    ensures \result == (start + end)/2;
    assigns \nothing;
 */
int mid(int start, int end)
{
    return (start + end) / 2;
}

/* Pour augmenter le nombre de valeurs possibles pour start et end sans créer d'overflow,
 * il faut changer leur type de variable : au lieu d'utiliser un int on peut utiliser un long,
 * et au lieu d'utiliser une variable signé, on peut utiliser une variable non-signé,
 * car on a pas besoin de valeurs négatives. La nouvelle version serait donc : */
/*@ requires 0 <= start + end <= ULLONG_MAX;
    ensures \result == (start + end)/2;
    assigns \nothing;
 */
unsigned long long mid_with_more_values(unsigned long long start, unsigned long long end)
{
    return (start + end) / 2;
}
/* Ici start et end sont des valeures comprises entre 0 et 2^64-1 ( 8 octets ), contre 0 à 2^15-1 ( 4 octets ( dont 2 inutilisés ) ) pour la version précédente  */

/* FEUILLE 2 */

/* Exercice 3 */
/*@
  requires \valid(value);
  requires INT_MIN <= *value+step <= INT_MAX;
  ensures \old(*value)+step == *value;
  assigns *value;
*/
void increment(int * value, int step)
{
    *value += step;
}

/* Exercice 4 */
/*@ ensures \result == 0 <==> p != NULL;
  ensures \result == 1 <==> p == NULL;
  assigns \nothing;
*/
int is_null(void * p)
{
    return p == NULL;
}



/* FEUILLE 3 */

/* Exercice 1 */

/*@ requires \valid(a + (0..size-1));
    assigns \nothing;
    behavior all_negative:
      assumes \forall integer k; 0 <= k < size ==> a[k] <= 0;
      ensures \result == true;
    behavior one_positive:
      assumes \exists integer k; 0 <= k < size && a[k] > 0;
      ensures \result == false;
    disjoint behaviors;
    complete behaviors; */
bool is_negative(int * a, size_t size)
{
    /*@ loop invariant 0 <= i <= size;
      @ loop invariant \forall integer k; 0 <= k < i ==> a[k]<=0;
      @ loop assigns i;
      @ loop variant size - i; */
    for(size_t i = 0; i < size; i++)
        if (a[i] > 0)
            return false;
    return true;
}


/* Exercice 3 */

/*@ requires INT_MIN < size1 + size2 < INT_MAX;
    requires \valid(t1 + (0..size1-1));
    requires \valid(t2 + (0..size2-1));
    requires \valid(dst + (0..size1+size2-1));
    requires \separated(t1 + (0..size1-1),t2 + (0..size2-1));
    requires \separated(t1 + (0..size1-1),dst + (0..size1+size2-1));
    requires \separated(t2 + (0..size2-1),dst + (0..size1+size2-1));
    assigns *(dst + (0..size1+size2-1));
    ensures \forall integer i; 0<=i<size1 ==> dst[i] == t1[i];
    ensures \forall integer i; size1<=i<size1+size2 ==> dst[i] == t2[i-size1];
     */
void concat(int * t1, size_t size1, int * t2, size_t size2, int * dst)
{
    /*@
      loop invariant 0 <= i <= size1 + size2;
      loop invariant \forall integer k; 0 <= k < size1 && k<i ==> dst[k] == t1[k];
      loop invariant \forall integer k; size1 <= k < size1+size2 && k<i ==> dst[k] == t2[k-size1];
      loop assigns i;
      loop assigns *(dst + (0..size1+size2-1));
      loop variant size1 + size2 - i;
      */
    for(size_t i = 0; i < size1 + size2; i++){
        if (i < size1)
            dst[i] = t1[i];
        else
            dst[i] = t2[i - size1];
    }
}
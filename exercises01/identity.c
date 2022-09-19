int incr(int x){ return x + 1; }

int decr(int x){ return x - 1; }

int identity(int x){
  int tmp = decr(x);
  tmp = incr(tmp);
  return tmp;
}

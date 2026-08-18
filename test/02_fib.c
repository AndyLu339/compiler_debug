// 02_fib.c — 递归斐波那契
int fib(int n) {
  if (n <= 1)
    return n;
  return fib(n - 1) + fib(n - 2);
}

int main() {
  return fib(10);
}

// 08_is_prime.c — 试除法判素数
// 期望返回值: 1  (97 是素数)

int is_prime(int n) {
  if (n < 2)
    return 0;
  int i = 2;
  while (i * i <= n) {
    if (n % i == 0)
      return 0;
    i = i + 1;
  }
  return 1;
}

int main() {
  return is_prime(97);
}

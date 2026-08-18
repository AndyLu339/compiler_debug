// 09_power.c — 快速幂（递归）
// 期望返回值: 1024  (2^10 = 1024)

int power(int base, int exp) {
  if (exp == 0)
    return 1;
  int half = power(base, exp / 2);
  if (exp % 2 == 0)
    return half * half;
  return half * half * base;
}

int main() {
  return power(2, 10);
}

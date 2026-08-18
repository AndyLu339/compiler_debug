// 12_collatz.c — Collatz 序列长度
// 期望返回值: 111  (从 27 到 1 需要 111 步)

int collatz(int n) {
  int count = 0;
  while (n != 1) {
    if (n % 2 == 0)
      n = n / 2;
    else
      n = 3 * n + 1;
    count = count + 1;
  }
  return count;
}

int main() {
  return collatz(27);
}

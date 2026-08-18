// 13_perfect_num.c — 完全数判定
// 期望返回值: 1  (28 = 1 + 2 + 4 + 7 + 14, 是完全数)

int is_perfect(int n) {
  int sum = 0;
  int i = 1;
  while (i < n) {
    if (n % i == 0)
      sum = sum + i;
    i = i + 1;
  }
  if (sum == n)
    return 1;
  return 0;
}

int main() {
  return is_perfect(28);
}

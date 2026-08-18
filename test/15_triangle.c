// 15_triangle.c — 三角形数
// 期望返回值: 55  (第 10 个三角形数 = 1+2+...+10 = 55)

int tri(int n) {
  int sum = 0;
  int i = 1;
  while (i <= n) {
    sum = sum + i;
    i = i + 1;
  }
  return sum;
}

int main() {
  return tri(10);
}

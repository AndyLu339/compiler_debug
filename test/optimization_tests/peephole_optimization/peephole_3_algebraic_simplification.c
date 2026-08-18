int main() {
    int x = 10;
    int y = x + 0; // Should simplify to y = x
    int z = x * 1; // Should simplify to z = x
    int w = x - 0; // Should simplify to w = x
    int v = x / 1; // Should simplify to v = x
    return y + z + w + v;
}



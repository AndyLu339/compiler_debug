int add(int p1, int p2) {
    return p1 + p2;
}
int subtract(int p1, int p2) {
    return p1 - p2;
}
int get_five() {
    return 5;
}
int main() {
    int a = 10;
    int b = 5;
    int result = 0;
    result = (add(a, b) + subtract(a, b)) * get_five();
    return result;
}



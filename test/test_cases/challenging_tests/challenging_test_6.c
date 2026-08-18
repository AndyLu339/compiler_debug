
int get_value(int num) {
    return num;
}
int add(int p1, int p2) {
    return p1 + p2;
}
int main() {
    int a = 10;
    int b = 20;
    int func_param_test = add(get_value(a), get_value(b));
    return func_param_test;
}



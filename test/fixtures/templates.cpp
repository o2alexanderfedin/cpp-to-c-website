// Template functions
template<typename T>
T maximum(T a, T b) {
    return (a > b) ? a : b;
}

template<typename T>
void swapValues(T& a, T& b) {
    T temp = a;
    a = b;
    b = temp;
}

template<typename T>
class Stack {
private:
    T* items;
    int top;
    int capacity;

public:
    Stack(int size) : capacity(size), top(-1) {
        items = new T[capacity];
    }

    ~Stack() {
        delete[] items;
    }

    void push(T item) {
        if (top < capacity - 1) {
            items[++top] = item;
        }
    }

    T pop() {
        if (top >= 0) {
            return items[top--];
        }
        return T();
    }

    bool isEmpty() const {
        return top == -1;
    }

    int size() const {
        return top + 1;
    }
};

// Pointer operations
void swap(int* a, int* b) {
    int temp = *a;
    *a = *b;
    *b = temp;
}

int* createArray(int size) {
    int* arr = new int[size];
    for (int i = 0; i < size; i++) {
        arr[i] = i * 2;
    }
    return arr;
}

void deleteArray(int* arr) {
    delete[] arr;
}

struct Node {
    int data;
    Node* next;
};

Node* createNode(int value) {
    Node* node = new Node;
    node->data = value;
    node->next = nullptr;
    return node;
}

void appendNode(Node* head, int value) {
    Node* current = head;
    while (current->next != nullptr) {
        current = current->next;
    }
    current->next = createNode(value);
}

int countNodes(Node* head) {
    int count = 0;
    Node* current = head;
    while (current != nullptr) {
        count++;
        current = current->next;
    }
    return count;
}

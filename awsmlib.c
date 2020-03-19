//compile with clang: clang-9 --target=wasm32 -nostdlib -Wl,--export-all -Wl,--no-entry -O3 -Wl,-no-gc-sections awsmlib.c -Wl,--allow-undefined  -o awsmlib.wasm 

typedef long long i64;
typedef unsigned char u8;
typedef unsigned long u32;

i64 get_heap_size();
void set_heap_size(i64 newsize);

i64 heap_start = 0;
i64 heap_end = 0;

void init_alloc(){
  static int alloc_inited = 0;
  if(alloc_inited == 0){
    alloc_inited = 1;
    heap_start = get_heap_size();
    heap_end = heap_start + 128000;
    set_heap_size(heap_end);
  }
}

void resize_heap(i64 bytes){
  if(bytes > heap_end - heap_start){
    set_heap_size(bytes + heap_start);
    heap_end = bytes + heap_start;
  }
}

void * _alloc(int bytes){
  init_alloc();
  static i64 alloc_offset = -1;
  if(alloc_offset == -1){
    alloc_offset = heap_start + 1;
  }
  void * ptr = (void *) alloc_offset;
  alloc_offset += bytes;
  if(alloc_offset > heap_end)
    resize_heap((heap_start - heap_end) * 2);

  return ptr;
}

void * alloc(int bytes){
  return _alloc(bytes);
}


void * memset(void * ptr, int value, u32 count){
  u8 * _ptr;
  for(i64 i; i < count; i++)
    _ptr[i] = (u8) value;
  return _ptr;
}

int print_str(const char * x);
void print_i32(int x);
void print_f32(float x);

// error handling. these functions causes an exception to be thrown in the interpreter.
void awsm_error(const char * e);
void error(const char * e){ awsm_error(e); }
#define ASSERT(expr) if(!(expr)){error("Assertion '" #expr "' Failed");}

//void print_f64(double x);
void require_i32(int x, int y);
int awsm_fork();
unsigned long long new_coroutine(void (* f)(void * arg), void * arg);
void yield();
int fib(int n){
  //print_i32(n);
  if(n <2)
    return 1;
  return fib(n - 1) + fib(n - 2);
}

void inscribe(char * x){
  x[0] = 'a';
  x[1] = '\n';
}
float x, y2;
void incr_y(){
  y2 += 0.1;
  print_f32(y2);
}

void test_fork(){
  //int forkid = awsm_fork();
  //print_i32(forkid);
  if(awsm_fork()){
   print_str("fork\n");
 }else{
   print_str("other fork\n");
 }
}

typedef struct{
  float x, y;
}vec2;

vec2 vec2_new(float x, float y){
  return (vec2){.x = x, .y = y};
}

void vec2_print(vec2 v){
  print_str("("); 
  print_f32(v.x);
  print_str(",");
  print_f32(v.y);
  print_str(")"); 
}

void subthing(){
  print_i32(fib(15));
  print_str("\ncalc!\n");
}

int main(){
  print_str("Hello World!\n");
  return 0;
}

int test_main(){
  vec2 v = vec2_new(1.0, -1.5);
  float x = 0;
  for(float y = 0.2; y < 5; y*=2){
    x += y + y2;
    y2 = y2 + 0.01;
  }
  print_f32(y2);
  print_str(" ");
  print_f32(x);
  print_str("\n");
  
  subthing();
  
  require_i32(987, fib(15));
  return 5;
}

void main_forked(){
  if(awsm_fork()){
    awsm_fork();
    main();
  }else{
    print_i32(fib(15));
    print_str("\n");
    if(awsm_fork()){
      main();
    }else{
      print_str("main ends\n");
    }
  }  
}

struct {
  i64 * a;
  i64 * b;
  u8 * type;

  i64 count;
  i64 end;
  
}cons;

typedef enum{
  // nil type. for all bits = 0 this means nil
  // for bits != 0 this means t
  TYPE_NIL = 0,
  TYPE_I64 = 1,
  TYPE_F64 = 2,
  TYPE_CONS = 3,
  TYPE_SYMBOL = 4,
  TYPE_MAX = 7
}etype;

#define TYPE_SHIFT 3

typedef enum{
  TYPE_CONS_CONS = 0,
  TYPE_CONS_STRING = 1,
  TYPE_CONS_ARRAY = 2
}econs_type;

i64 mknil(){ return 0; }

i64 mkcons(i64 a, i64 b){
  i64 c = (i64)cons.end;
  cons.end += 1;
  cons.a[c] = a;
  cons.b[c] = b;
  cons.type[c] = 0;
  return c << TYPE_SHIFT | TYPE_CONS;
}

i64 mki64(i64 a){
  return a << TYPE_SHIFT | TYPE_I64;
}

i64 unmki64(i64 a){
  return a >> TYPE_SHIFT;
}

int consp(i64 a){
  return (a & TYPE_MAX) == TYPE_CONS;
}

int integerp(i64 a){
  return (a & TYPE_MAX) == TYPE_I64;
}
int symbolp(i64 a){
  return (a & TYPE_MAX) == TYPE_SYMBOL;
}
int nilp(i64 a){
  return (a & TYPE_MAX) == TYPE_NIL;
}
i64 cdr(i64 a){
  return cons.b[a >> TYPE_SHIFT];
}

i64 car (i64 a){
  return cons.a[a >> TYPE_SHIFT];
}

i64 cons_type(i64 a){
  return cons.type[a >> TYPE_SHIFT];
}

i64 set_cons_type(i64 consi, i64 new_type){
  i64 tp = unmki64(new_type);
  cons.type[consi >> TYPE_SHIFT] = tp;
  return consi;
}


i64 stringp(i64 a){
  return mki64(consp(a) && cons_type(a) == TYPE_CONS_STRING);
}


char * symbol_name;
i64 symbol_offset;
i64 symbol_capacity;

i64 conslen(i64 a){
  i64 c = 0;
  while(consp(a)){
    c += 1;
    a = cdr(a);
  }
  return mki64(c);
}

i64 cons_print2(i64 a, i64 sub_print){
  static int printing_str_with_quotes = 1;
  if(integerp(a)){
    print_i32(unmki64(a));
  }else if(consp(a)){
    if(cons_type(a) == TYPE_CONS_STRING){
      if(printing_str_with_quotes)
	print_str("\"");
      while(consp(a)){
	i64 x = unmki64(car(a));
	char * xp = (char *) &x;
	xp[7] = 0;
	print_str(xp);
	a = cdr(a);
      }
      if(printing_str_with_quotes)      
	print_str("\"");
	    
    }else{
      if(!sub_print)
	print_str("(");
      cons_print2(car(a), 0);
      print_str(" ");

      cons_print2(cdr(a), 1);
      if(!sub_print)
	print_str(")");
    }
  }else if(symbolp(a)){
    a = a >> TYPE_SHIFT;
    i64 * consptr = (i64 *) (symbol_name + a);
    if(stringp(consptr[0])){
      printing_str_with_quotes = 0;
      cons_print2(consptr[0], 0);
      printing_str_with_quotes = 1;
    }else{
      print_str("sym");
      print_i32(a);
    }
  }else if(nilp(a) && !sub_print){
    print_str("nil");
  }else{
    print_str("??");
  }
  return mknil();
}

i64 cons_print(i64 a){
  cons_print2(a, 0);
  print_str("\n");
  return a;
}


int init_cons(){
  if(cons.a != 0) return 0;
  i64 * a = alloc(sizeof(i64) * 1024);
  i64 * b = alloc(sizeof(i64) * 1024);
  cons.a = a;
  cons.b = b;
  cons.type = alloc(sizeof(u8) * 1024);
  cons.count = 1024;

  symbol_name = alloc(sizeof(char) * 4096);
  symbol_offset = 0;
  symbol_capacity = 4096;
  
  return mki64(5);
}

char * symbol_ptr(i64 symbol){
  if((symbol & TYPE_MAX) != TYPE_SYMBOL)
    return 0;
  return symbol_name + (symbol >> TYPE_SHIFT);
}

i64 new_symbol(i64 symbol_length){
  i64 sym = symbol_offset;
  i64 start_offset = symbol_offset;
  symbol_offset += unmki64(symbol_length) + 1;
  sym = sym << TYPE_SHIFT | TYPE_SYMBOL;
  memset(symbol_name + start_offset, 0, symbol_offset - start_offset);
  return sym;
}


i64 new_symbol_named(i64 sym_name){
  ASSERT(consp(sym_name));
  ASSERT(cons_type(sym_name) == TYPE_CONS_STRING);
  i64 offset = new_symbol(mki64(sizeof(i64)));
  i64 * ptr = (i64 *) (symbol_name + offset);
  ptr[0] = sym_name;

  return offset << TYPE_SHIFT | TYPE_SYMBOL;
}

i64 logior(i64 a, i64 b){
  a = unmki64(a);
  b = unmki64(b);
  return mki64(a | b);
}

i64 logand(i64 a, i64 b){
  a = unmki64(a);
  b = unmki64(b);
  return mki64(a & b);
}

i64 ash(i64 a, i64 b){
  a = unmki64(a);
  b = unmki64(b);
  if( b < 0)
    return mki64(a >> -b);
  return mki64(a << b);
}


void string_to_buffer(i64 str, char * buf){
  while(consp(str)){
    i64 chunk = car(str);
    ((i64 *) buf)[0] = unmki64(chunk);
    buf += 7;
    str = cdr(str);
  }
}

void lisp_error(i64 err){
  static char buffer_error[100];
  
  ASSERT(stringp(err));
  string_to_buffer(err, buffer_error);
  //print_str(buffer_error);
  error(buffer_error);

}

void test_print(){
  print_str("test?\n");

  i64 v1 = mki64(53);
  i64 v2 = mki64(10);
  i64 c = mkcons(v1, v2);
  i64 c2 = mkcons(v1, c);
  i64 c3 = mkcons(v1, c2);
  print_i32(v1); print_str(" ");  print_i32(v2); print_str(" ");  print_i32(c); print_str("\n");
  print_i32(c2); print_str("\n");
  print_i32(conslen(c3)); print_str("\n");
  print_i32(unmki64(v1)); print_str("\n");
  print_i32(integerp(v1)); print_str("\n");
  print_i32(integerp(c2)); print_str("\n");
  print_i32(consp(c2)); print_str("\n");
}


int falloc(int bytes){
  return mki64((int) alloc(unmki64(bytes)));
}

i64 fprint(i64 ptr){
  char * ptr2 = (char *) unmki64(ptr);
  print_str(ptr2);
  return mknil();
}

i64 add2(i64 a, i64 b){ return mki64(unmki64(a) + unmki64(b)); }
i64 sub2(i64 a, i64 b){ return mki64(unmki64(a) - unmki64(b)); }
i64 mul2(i64 a, i64 b){ return mki64(unmki64(a) * unmki64(b)); }
i64 div2(i64 a, i64 b){ return mki64(unmki64(a) / unmki64(b)); }

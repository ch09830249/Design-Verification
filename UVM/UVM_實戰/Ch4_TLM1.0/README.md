# TLM Transaction Level Modeling（事務級建模）定義
* transaction 就是把具有某一特定功能的一組資訊封裝在一起而成為的一個類別
  如 my_transaction 就是把一個 MAC 幀裡的各個字段封裝在了一起
# TLM 通訊中有以下幾個常用的術語：
1. **put 操作**，通訊的發起者 A 把一個 transaction 傳送給 B  
   * 在這個過程中，A 稱為 "發起者"，而 B 稱為 "目標"  
   * A 具有的連接埠 (以方框表示) 稱為 PORT，而 B 的連接埠 (以圓圈表示) 稱為 EXPORT
   * 資料流是從 A 流向 B 的
2. **get 操作**，A 向 B 索取一個 transaction  
   * 在這個過程中，A 仍然是 "發起者"，B 仍然是 "目標"  
   * A 上的端口仍然是 PORT，而 B 上的埠還是 EXPORT
   * 資料流是從 B 流向 A 的
PS: PORT 和 EXPORT 體現的是**控制流而不是資料流**  
  因為在 put 操作中，資料流是從 PORT 流向 EXPORT 的，而在 get 操作中，資料是從 EXPORT 流向 PORT的
  但是無論是 get 還是 put 操作，其發起者擁有的都是 PORT 端口，而不是 EXPORT。作為一個 EXPORT 來說，只能被動地接收 PORT 的命令
![image](https://github.com/user-attachments/assets/8f72bf11-846e-4cf8-8d67-97207bb6a1b9)
3. **transport操作**，transport 操作相當於一次 put 操作加一次 get 操作
   * 這兩次操作的「發起者」都是 A，目標都是 B
   * A 上的連接埠依然是 PORT，而 B 上的連接埠依然是 EXPORT
   * 資料流先從 A 流向 B，再從 B 流向 A
   * 在現實世界中，相當於是 A 向 B 提交了一個請求（request），而 B 回傳給 A 一個應答（response） 
     所以這種 transport 操作也常常被稱為做 request-response 操作
![image](https://github.com/user-attachments/assets/03fd7dd4-efd1-4d13-aba6-ad72d46264f3)
# UVM 中的 PORT 與 EXPORT
UVM 提供對 TLM 操作的支持，在其中實現了 PORT 與 EXPORT。對應於不同的操作，有不同的 PORT，UVM 中常用的 PORT 有：
```
// Put * 3
uvm_blocking_put_port#(T);
uvm_nonblocking_put_port#(T);
uvm_put_port#(T);
// Get * 3
uvm_blocking_get_port#(T);
uvm_nonblocking_get_port#(T);
uvm_get_port#(T);
// Peek * 3
uvm_blocking_peek_port#(T);
uvm_nonblocking_peek_port#(T);
uvm_peek_port#(T);
// Get Peek * 3
uvm_blocking_get_peek_port#(T);
uvm_nonblocking_get_peek_port#(T);
uvm_get_peek_port#(T);
// Transport * 3
uvm_blocking_transport_port#(REQ, RSP);
uvm_nonblocking_transport_port#(REQ, RSP);
uvm_transport_port#(REQ, RSP);
```
* get_peek 系列端口集合了 get 操作和 peek 操作兩者的功能
* 前 12 個定義中的參數就是這個 PORT 中的資料流類型
* 最後 3 個定義中的參數則表示 transport 操作中**發起請求時傳輸的資料類型和傳回的資料類型**
* 這幾種 PORT 對應 TLM 中的操作，同時以 blocking 和 nonblocking 關鍵字區分
* 對於名稱中不含這兩者的，則表示這個連接埠既可以用作是阻塞的，也可以用作是非阻塞的，否則只能用於阻塞的或只能用於非阻塞的
UVM 中常用的 EXPORT 有：
```
uvm_blocking_put_export#(T);
uvm_nonblocking_put_export#(T);
uvm_put_export#(T);
uvm_blocking_get_export#(T);
uvm_nonblocking_get_export#(T);
uvm_get_export#(T);
uvm_blocking_peek_export#(T);
uvm_nonblocking_peek_export#(T);
uvm_peek_export#(T);
uvm_blocking_get_peek_export#(T);
uvm_nonblocking_get_peek_export#(T);
uvm_get_peek_export#(T);
uvm_blocking_transport_export#(REQ, RSP);
uvm_nonblocking_transport_export#(REQ, RSP);
uvm_transport_export#(REQ, RSP);
```
PORT 和 EXPORT 體現的是一種控制流，在這種控制流中，PORT 具有高優先級，而 EXPORT 具有低優先級。只有高優先級的連接埠才能向低優先權的連接埠發起三種操作
# UVM 中各種連接埠的互連
## PORT 與 EXPORT 的連接
* UVM 中使用 connect 函數來建立連線關係。  
  如 A 要和 B 通訊（A 是發起者），那麼可以這麼寫：  
  A.port.connect（B.export），但是不能寫成 B.export.connect（A.port）。
* 只有發起者才能呼叫 connect 函數，而被動承擔者則作為 connect 的參數。
* **Class A 的 code**
```
class A extends uvm_component;
  `uvm_component_utils(A)
  uvm_blocking_put_port#(my_transaction) A_port;  // 宣告該 PUT PORT
…
endclass

function void A::build_phase(uvm_phase phase);
  super.build_phase(phase);
  A_port = new("A_port", this);    // 實例化該 PUT PORT，第一個參數是名字，第二個參數則是一個 uvm_component 類型的父結點變數
endfunction

task A::main_phase(uvm_phase phase);
endtask
```
以下為 PORT 的 new 函數
```
function new(string name,
             uvm_component parent,
             int min_size = 1;
             int max_size = 1);
```
new 函數中的 min_size 和 max_size 指的是必須連接到這個 PORT 的下級連接埠數量的最小值和最大值，也即這一個 PORT 應該呼叫的connect 函數的最小值和最大值。如果採用默認值，即 min_size = max_size = 1，則只能連接一個 EXPORT
* **Class B 的 code**
```
class B extends uvm_component;
  `uvm_component_utils(B)
  uvm_blocking_put_export#(my_transaction) B_export;  // 宣告該 PUT EXPORT
  …
endclass

function void B::build_phase(uvm_phase phase);
  super.build_phase(phase);
  B_export = new("B_export", this);    // 一樣實例化
endfunction

task B::main_phase(uvm_phase phase);
endtask
```
在 env 中建立兩者之間的連結：
```
class my_env extends uvm_env;

  A A_inst;
  B B_inst;
  …

  virtual function void build_phase(uvm_phase phase);
    …
    A_inst = A::type_id::create("A_inst", this);
    B_inst = B::type_id::create("B_inst", this);
  endfunction
  …

endclass

function void my_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  A_inst.A_port.connect(B_inst.B_export);  // 連接兩個 component
endfunction
```
## UVM 中的 IMP
IMP 承擔了 UVM 中 TLM 的絕大部分實作程式碼
```
uvm_blocking_put_imp#(T, IMP);
uvm_nonblocking_put_imp#(T, IMP);
uvm_put_imp#(T, IMP);
uvm_blocking_get_imp#(T, IMP);
uvm_nonblocking_get_imp#(T, IMP);
uvm_get_imp#(T, IMP);
uvm_blocking_peek_imp#(T, IMP);
uvm_nonblocking_peek_imp#(T, IMP);
uvm_peek_imp#(T, IMP);
uvm_blocking_get_peek_imp#(T, IMP);
uvm_nonblocking_get_peek_imp#(T, IMP);
uvm_get_peek_imp#(T, IMP);
uvm_blocking_transport_imp#(REQ, RSP, IMP);
uvm_nonblocking_transport_imp#(REQ, RSP, IMP);
uvm_transport_imp#(REQ, RSP, IMP);
```
* IMP 定義中的 blocking、nonblocking、put、get、peek、get_peek、transport 等關鍵字不是它們發起做對應類型的操作，而只意味著它們可以和相應類型的 PORT 或 EXPORT 進行通信，且通信時作為被動承擔者
* 依照控制流的優先排序，IMP的優先權最低，一個 PORT 可以連接到一個 IMP，並發起三種操作，反之則不行
* 前六個 IMP 定義中的**第一個參數 T 是這個 IMP 傳輸的資料型態**。**第二個參數 IMP，為實現這個介面的一個 component (就是該 port 所在 component 的 pointer)**
* **Class A 的 code**
```
class A extends uvm_component;
  `uvm_component_utils(A)
  uvm_blocking_put_port#(my_transaction) A_port;
  …
endclass
…

task A::main_phase(uvm_phase phase);
  my_transaction tr;
  repeat(10) begin
    #10;
    tr = new("tr");
    assert(tr.randomize());
    A_port.put(tr);    // 發送 transaction
  end
endtask
```
* **Class B 的 code**
```
class B extends uvm_component;
  `uvm_component_utils(B)
  uvm_blocking_put_export#(my_transaction) B_export;
  uvm_blocking_put_imp#(my_transaction, B) B_imp;
  …
endclass
…
function void B::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  B_export.connect(B_imp);    // 將 B 的 export 連接到 imp
endfunction

function void B::put(my_transaction tr);      // Class B 實作 put 函數, 單純 print 出來
  `uvm_info("B", "receive a transaction", UVM_LOW)
  tr.print();
endfunction
```
PS: 在 B 的程式碼中，關鍵是要實作一個 put 函數/任務。如果不實現，將會給出如下的錯誤提示：
```
# ** Error: /home/landy/uvm/uvm-1.1d/src/tlm1/uvm_imps.svh(85): No field named 'put'.
# Region: /uvm_pkg::uvm_blocking_put_imp #(top_tb_sv_unit::my_transact
ion, top_tb_sv_unit::B)
```
* env 的 code 相同，連接 A 的 port 到 B 的 export
* IMP 是作為連結的終點。在 UVM 中，只有 IMP 才能作為連結關係的終點。如果是 PORT 或 EXPORT 作為終點，則會報錯
## PORT 與 IMP 的連接
![image](https://github.com/user-attachments/assets/07eb0e42-0acb-4ebb-b7bc-fa5002fd108b)  
| **Port 類型 (`A_port`)**           | **Imp 類型 (`B_imp`)**            | **B 中需定義的方法**                                                                                                                                                                                           |
| -------------------------------- | ------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `uvm_nonblocking_put_port`       | `uvm_nonblocking_put_imp`       | `function bit try_put(input T t);` <br> `function bit can_put();`                                                                                                                                       |
| `uvm_put_port`                   | `uvm_put_imp`                   | `task put(input T t);` <br> `function bit try_put(input T t);` <br> `function bit can_put();`                                                                                                           |
| `uvm_blocking_get_port`          | `uvm_blocking_get_imp`          | `task get(output T t);`                                                                                                                                                                                 |
| `uvm_nonblocking_get_port`       | `uvm_nonblocking_get_imp`       | `function bit try_get(output T t);` <br> `function bit can_get();`                                                                                                                                      |
| `uvm_get_port`                   | `uvm_get_imp`                   | `task get(output T t);` <br> `function bit try_get(output T t);` <br> `function bit can_get();`                                                                                                         |
| `uvm_blocking_peek_port`         | `uvm_blocking_peek_imp`         | `task peek(output T t);`                                                                                                                                                                                |
| `uvm_nonblocking_peek_port`      | `uvm_nonblocking_peek_imp`      | `function bit try_peek(output T t);` <br> `function bit can_peek();`                                                                                                                                    |
| `uvm_peek_port`                  | `uvm_peek_imp`                  | `task peek(output T t);` <br> `function bit try_peek(output T t);` <br> `function bit can_peek();`                                                                                                      |
| `uvm_blocking_get_peek_port`     | `uvm_blocking_get_peek_imp`     | `task get(output T t);` <br> `task peek(output T t);`                                                                                                                                                   |
| `uvm_nonblocking_get_peek_port`  | `uvm_nonblocking_get_peek_imp`  | `function bit try_get(output T t);` <br> `function bit can_get();` <br> `function bit try_peek(output T t);` <br> `function bit can_peek();`                                                            |
| `uvm_get_peek_port`              | `uvm_get_peek_imp`              | `task get(output T t);` <br> `function bit try_get(output T t);` <br> `function bit can_get();` <br> `task peek(output T t);` <br> `function bit try_peek(output T t);` <br> `function bit can_peek();` |
| `uvm_blocking_transport_port`    | `uvm_blocking_transport_imp`    | `task transport(input T req, output T rsp);`                                                                                                                                                            |
| `uvm_nonblocking_transport_port` | `uvm_nonblocking_transport_imp` | `function bit nb_transport(input T req, output T rsp);`                                                                                                                                                 |
| `uvm_transport_port`             | `uvm_transport_imp`             | `task transport(input T req, output T rsp);` <br> `function bit nb_transport(input T req, output T rsp);`                                                                                               |

在前述的這些規律中，對於所有blocking系列的連接埠來說，可以定義對應的任務或函數，如對於blocking_put連接埠來說，可以定
義名字為put的任務，也可以定義名字為put的函數。這是因為A會呼叫B中名字為put的接口，而不管這個接口的型別。由於A中的
put是個任務，所以B中的put可以是任務，也可以是函數。但是對於nonblocking系列連接埠來說，只能定義函數。
## EXPORT 與 IMP 的連接
PORT 可以與 IMP 連接，同樣的 EXPORT 也可以與IMP相連接，其連接方法與 PORT 和 IMP 的連接完全一樣
```
function void my_env::connect_phase(uvm_phase phase);
          super.connect_phase(phase);
          A_inst.A_export.connect(B_inst.B_imp);  // 就是將 A_port 改成 A_export
endfunction
```
## PORT 與 PORT 的連接
![image](https://github.com/user-attachments/assets/edb3c087-d918-4bf1-a3a2-12dfdca2404d)
上圖中，A 與 C 中是 PORT，B 中是 IMP。UVM 支援 C 的 PORT 連接到 A 的 PORT，並最終連接到 B 的 IMP
* **Class C code (類似 driver)**
```
class C extends uvm_component;
  `uvm_component_utils(C)
  uvm_blocking_put_port#(my_transaction) C_port;
  …
endclass
…
task C::main_phase(uvm_phase phase);
  my_transaction tr;
  repeat(10) begin
    #10;
    tr = new("tr");
    assert(tr.randomize());
    C_port.put(tr);
  end
endtask
```
* **Class A code (類似 agent)**
```
class A extends uvm_component;
  `uvm_component_utils(A)
  C C_inst;
  uvm_blocking_put_port#(my_transaction) A_port;
  …
endclass

function void A::build_phase(uvm_phase phase);
  super.build_phase(phase);
  A_port = new("A_port", this);                     // 實例化 A_port
  C_inst = C::type_id::create("C_inst", this);      // 實例化 Class C
endfunction

function void A::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  C_inst.C_port.connect(this.A_port);     // 在 class A 的 connect 連接
endfunction

task A::main_phase(uvm_phase phase);
endtask
```
## EXPORT 與 EXPORT 的連接
![image](https://github.com/user-attachments/assets/0a0477c6-5ba2-4572-a500-5b721027c6a8)
* **Class C code (類似 C: agent, B: monitor)**
```
class C extends uvm_component;
  `uvm_component_utils(C)
  B B_inst;
  uvm_blocking_put_export#(my_transaction) C_export;
  …
endclass

function void C::build_phase(uvm_phase phase);
  super.build_phase(phase);
  C_export = new("C_export", this);              // 實例化 C_export
  B_inst = B::type_id::create("B_inst", this);   // 實例化 Class B
endfunction

function void C::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  this.C_export.connect(B_inst.B_export);        // 連接 Class C 內部的連接 (C->B)
endfunction

task C::main_phase(uvm_phase phase);
endtask
```
* **env**
```
function void my_env::connect_phase(uvm_phase phase);
              super.connect_phase(phase);
              A_inst.A_port.connect(C_inst.C_export); // 連接 A->C
endfunction
```
## port export imp 比較
* **imp (Implementation)**
  * 真正實作介面方法的端口
  * 是最底層，實作者端
  * 常見於 monitor、driver 或實際功能模組中。
* **export**
  * 代表一個實作了 interface 的元件（例如有 imp）
  * 是一個**中介轉接點**，不實作方法，只是轉發到 imp
  * 可以在層級架構中向上暴露 imp 的功能，讓其他元件可以透過 export 呼叫
* **port**
  * 主動方：會呼叫一個介面方法（例如 put()）
  * 通常由上層元件發起呼叫  
![image](https://github.com/user-attachments/assets/e722a5ed-6524-4fa4-8aef-491a8961297a)

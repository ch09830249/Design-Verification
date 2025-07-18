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
## blocking_get 端口的使用
* 使用 blocking_get 系列連接埠的框圖如下圖所示
![image](https://github.com/user-attachments/assets/547d9eef-20d0-4c8d-8b2e-75280b9dd3d5)
在這種連結關係中，資料流依然是從 A 到 B，但 A 由動作發起者變成了動作接收者，而 B 由動作接收者變成了動作發起者。B_port 的型別為 uvm_blocking_get_port，A_export 的型別為 uvm_blocking_get_export，A_imp 的型別為 uvm_blocking_get_imp
* uvm_blocking_get_imp 所在的 component 要實作一個名字為 get 的函數/任務
* **Class A code 如下:**
```
class A extends uvm_component;
  `uvm_component_utils(A)
  uvm_blocking_get_export#(my_transaction) A_export;
  uvm_blocking_get_imp#(my_transaction, A) A_imp;
  my_transaction tr_q[$];
endclass

function void A::build_phase(uvm_phase phase);
  super.build_phase(phase);
  A_export = new("A_export", this);
  A_imp = new("A_imp", this);
endfunction

function void A::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  A_export.connect(A_imp);    //  在 A 的 connect_phase，需要把 A_export 和 A_imp 連接起來。
endfunction

/*
  在 A 的 get 任務中，每隔 2 個時間單位檢查 tr_q 中是否有數據，如果有則發送出去
  當 B 在其 main_phase 呼叫 get 任務時，會最終執行 A 的 get 任務。
*/
task A::get(output my_transaction tr);
  while (tr_q.size() == 0) #2;
  tr = tr_q.pop_front();
endtask

// A 每隔 10 sec 產生並塞一個新的 transaction 到 queue 中
task A::main_phase(uvm_phase phase);
  my_transaction tr;
  repeat (10) begin
    #10;
    tr = new("tr");
    tr_q.push_back(tr);
  end
endtask
```
* **Class B code 如下:**
```
class B extends uvm_component;
  `uvm_component_utils(B)
  uvm_blocking_get_port#(my_transaction) B_port;
endclass

function void B::build_phase(uvm_phase phase);
  super.build_phase(phase);
  B_port = new("B_port", this);
endfunction

task B::main_phase(uvm_phase phase);
  my_transaction tr;
  // 無限迴圈 get transaction 並印出
  while (1) begin
    B_port.get(tr);
    `uvm_info("B", "get a transaction", UVM_LOW)
    tr.print();
  end
endtask
```
* **env code 如下:**
```
function void my_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  B_inst.B_port.connect(A_inst.A_export);
endfunction
```
* 需要謹記的是連結的終點必須是一個 IMP
## blocking_transport 端口的使用
* 在 transport 系列連接埠中，通信變成了雙向的
![image](https://github.com/user-attachments/assets/22c8e65d-83a6-4b2c-818a-e3da26f03533)
* **Class A code 如下:**
```
class A extends uvm_component;
  `uvm_component_utils(A)
  uvm_blocking_transport_port#(my_transaction, my_transaction) A_transport;
endclass
......
task A::main_phase(uvm_phase phase);
  my_transaction tr;
  my_transaction rsp;
  repeat (10) begin
    #10;
    tr = new("tr");
    assert(tr.randomize());
    A_transport.transport(tr, rsp);  // 在 A 中呼叫 transport 任務，並把生成的 transaction 當作第一個參數
    `uvm_info("A", "received rsp", UVM_MEDIUM)
    rsp.print();                     // A 根據接收到的 rsp 決定後面的行為
  end
endtask
```
* **Class B code 如下:**
```
class B extends uvm_component;
  `uvm_component_utils(B)
  uvm_blocking_transport_imp#(my_transaction, my_transaction, B) B_imp;
endclass

// B 中的 transaport 任務接收到這筆 transaction，根據這筆 transaction 做某些操作，並把操作的結果當作 transport 的第二個參數送出
task B::transport(my_transaction req, output my_transaction rsp);
  `uvm_info("B", "receive a transaction", UVM_LOW)
  req.print();
  // do something according to req
  #5;
  rsp = new("rsp");
endtask
```
* **env code 如下:**
```
function void my_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  A_inst.A_transport.connect(B_inst.B_imp);
endfunction
```
## nonblocking 端口的使用
* nonblocking 的所有操作都是非阻塞的，換言之，**必須用函數實現，而不能用任務實現**
![image](https://github.com/user-attachments/assets/2106d6dc-db20-47fe-be60-79ca90be6266)
* **Class A code 如下:**
```
class A extends uvm_component;
  `uvm_component_utils(A)
  uvm_nonblocking_put_port#(my_transaction) A_port;
......
endclass

task A::main_phase(uvm_phase phase);
  my_transaction tr;
  repeat (10) begin
    tr = new("tr");
    assert(tr.randomize());
    while (!A_port.can_put()) #10;
    void'(A_port.try_put(tr));
  end
endtask
```
* 由於連接埠變成了非阻塞的，所以在送出 transaction 之前需要呼叫 can_put 函數來確認是否能夠執行 put 操作。can_put 最終會調用 B 中的 can_put
* **Class B code 如下:**
```
class B extends uvm_component;
  `uvm_component_utils(B)
  uvm_nonblocking_put_imp#(my_transaction, B) B_imp;
  my_transaction tr_q[$];
......
endclass

// 確認 queue 中是否有 transaction
function bit B::can_put();
  if (tr_q.size() > 0)
    return 0;
  else
    return 1;
endfunction

function bit B::try_put(my_transaction tr);
  `uvm_info("B", "receive a transaction", UVM_LOW)
  if (tr_q.size() > 0)
    return 0;
  else begin
    tr_q.push_back(tr);
    return 1;
  end
endfunction

task B::main_phase(uvm_phase phase);
  my_transaction tr;
  while (1) begin
    if (tr_q.size() > 0)
      tr = tr_q.pop_front();
    else
      #25;
  end
endtask
```
* 在 A 中使用 can_put 來判斷是否可以發送，其實這裡還可以不用 can_put，而直接使用 try_put
* 如果不使用 can_put，在 B 中仍然需要定義一個名字為 can_put 的函數，這個函數裡可以沒有任何內容，純粹是空函數
* **env code 如下:**
```
function void my_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  A_inst.A_export.connect(B_inst.B_imp);
endfunction
```
## UVM 中 analysis 端口
UVM 中還有 2 種特殊的端口：**analysis_port 和 analysis_export**
1. 一個 analysis_port（analysis_export）可以連接多個 IMP，也就是說，analysis_port（analysis_export）與 IMP
之間的通信是一對多的通信 (put 和 get 系列端口與相應 IMP 的通信是一對一的通信) analysis_port（analysis_export）更像是一個廣播
2. 對於 analysis_port 和 analysis_export 來說，沒有阻塞和非阻塞的概念。因為它本身就是廣播，不必等待與其相連的其他連接埠的回應，所以不存在阻塞和非阻塞
3. 一個 analysis_port 可以和多個 IMP 連接進行通信，但是 IMP 的類型必須是 uvm_analysis_imp，否則會報錯
4. 對於 analysis_port 和 analysis_export 來說，只有一種操作：write。在 analysis_imp 所在的 component，必須定義一個名字為 write 的函式  
![image](https://github.com/user-attachments/assets/d0a00e32-c9d6-4668-9c3d-6a885b371f8d)
* **Class A code 如下:**
```
class A extends uvm_component;
  `uvm_component_utils(A)
  uvm_analysis_port#(my_transaction) A_ap;
…
endclass
…
// 只是簡單定義一個 analysis_port，並在 main_phase 中每隔 10 個時間單位寫入一個 transaction
task A::main_phase(uvm_phase phase);
  my_transaction tr;
  repeat(10) begin
    #10;
    tr = new("tr");
    assert(tr.randomize());
    A_ap.write(tr);
  end
endtask
```
* **Class B code 如下:**
```
class B extends uvm_component;
  `uvm_component_utils(B)
  uvm_analysis_imp#(my_transaction, B) B_imp;
  …
endclass
// B 是 B_imp 所在的 component，因此在 B 中定義一個名字為 write 的函數
function void B::write(my_transaction tr);
  `uvm_info("B", "receive a transaction", UVM_LOW)
  tr.print();
endfunction
```
* **env code 如下:**
```
/*
A_ap 分別與 B 和 C 中對應的 imp 連結到了一起。analysis_export 和 IMP 也可以這樣連接，只需將上面範例中的 uvm_analysis_port 改為 uvm_analysis_export 就可以
*/
function void my_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  A_inst.A_ap.connect(B_inst.B_imp);
  A_inst.A_ap.connect(C_inst.C_imp);
endfunction
```
PS: 與 put 系列連接埠的 PORT 和 EXPORT 直接相連會出錯的情況一樣，analysis_port 如果和一個 analysis_export 直接相連也會出錯。只有在 analysis_export 後面再連接一級 uvm_analysis_imp，才不會出錯。
## 一個 component 內有多個 IMP
之前範例 o_agt 的 monitor 與 scoreboard 之間的通信，使用 analysis_port 實作
* **monitor code 如下:**
```
class monitor extends uvm_monitor;
    uvm_analysis_port#(my_transaction) ap;    // 宣告 uvm_analysis_port
    task main_phase(uvm_phase phase);
        super.main_phase(phase);
        my_transaction tr;
        …
        ap.write(tr);      // write tr
        …
    endtask
endclass
```
* **scoreboard code 如下:**
```
class scoreboard extends uvm_scoreboard;
      uvm_analysis_imp#(my_transaction, scoreboard) scb_imp;
      task write(my_transaction tr);    // 實作 write task
            //do something on tr
      endtask
endclass
```
之後在 env 中可以使用 connect 連線。由於 monitor 與 scoreboard 在 UVM 樹中並不是平等的兄妹關係，其中間還間隔了 o_agt，所
這裡有三種連結方式
**1. 直接在 env 中跨層次引用 monitor 中的 ap**
* **env code 如下:**
```
function void my_env::connect_phase(uvm_phase phase);
      o_agt.mon.ap.connect(scb.scb_imp);
      …
endfunction
```
**2. 在 agent 中宣告一個 ap 並實例化它，在 connect_phase 將其與 monitor 的 ap 相連，並且可以在 env 中把 agent 的 ap 直接連接到 scoreboard 的 imp**
* **agent code 如下:**
```
class my_agent extends uvm_agent ;
    uvm_analysis_port #(my_transaction) ap;    // 宣告 ap
    …

    function void build_phase(uvm_phase phase);
          super.build_phase(phase);
          ap = new("ap", this);    // 實例化 ap
          …
    endfunction

    function void my_agent::connect_phase(uvm_phase phase);
        mon.ap.connect(this.ap);
        …
    endfunction
endclass

function void my_env::connect_phase(uvm_phase phase);
    o_agt.ap.connect(scb.scb_imp);
    …
endfunction
```
**3. 在 agent 中宣告一個 ap，但不實例化它，讓其指向 monitor 中的 ap。在 env 中可以直接連接 agent 的 ap 到 scoreboard 的 imp**
```
class my_agent extends uvm_agent ;
        uvm_analysis_port #(my_transaction) ap;
        …
        function void my_agent::connect_phase(uvm_phase phase);
              ap = mon.ap;
              …
        endfunction
endclass
function void my_env::connect_phase(uvm_phase phase);
    o_agt.ap.connect(scb.scb_imp);
    …
endfunction
```

* 第一種最簡單，但是其層次關係並不好，第二種稍顯麻煩，第三種既具有明顯的層次關係，同時其實作也較簡單
* 在上面的例子中，scoreboard 只接收一路數據，但在現實情況中，scoreboard 除了接收 monitor 的資料之外，還要接收 reference model的資料。對應的 scoreboard 就要再增加一個 uvm_analysis_imp 的 IMP，如 model_imp。此時問題就出現了，由於**收到的兩路資料應該要做不同的處理，所以這個新的 IMP 也要有一個 write 任務與其對應。但 write 只有一個**，怎麼辦？
UVM 考慮到了這種情況，它定義了一個宏 uvm_analysis_imp_decl 來解決這個問題，其使用方式為：
```
/*
程式碼透過宏 uvm_analysis_imp_decl 聲明了兩個後綴 _monitor 和 _model。
UVM 會根據這兩個後綴定義兩個新的 IMP 類別：uvm_analysis_imp_monitor 和 uvm_analysis_imp_model
*/
`uvm_analysis_imp_decl(_monitor)
`uvm_analysis_imp_decl(_model)

class my_scoreboard extends uvm_scoreboard;
  my_transaction expect_queue[$];

  uvm_analysis_imp_monitor#(my_transaction, my_scoreboard) monitor_imp;
  uvm_analysis_imp_model#(my_transaction, my_scoreboard) model_imp;
/*
當與 monitor_imp 相連接的 analysis_port 執行 write 函數時，會自動呼叫 write_monitor 函數，
而與 model_imp 相連接的 analysis_port 執行 write 函數時，會自動呼叫 write_model 函數
*/
  extern function void write_monitor(my_transaction tr);
  extern function void write_model(my_transaction tr);
  extern virtual task main_phase(uvm_phase phase);
endclass
```
* **scoreboard code 如下:**
```
function void my_scoreboard::write_model(my_transaction tr);
  expect_queue.push_back(tr);
endfunction

function void my_scoreboard::write_monitor(my_transaction tr);
  my_transaction tmp_tran;
  bit result;
  if(expect_queue.size() > 0) begin
    …
  end
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
## 使用 FIFO 通信
利用 FIFO 來實作 monitor 和 scoreboard 的通訊
在 agent 和 scoreboard 之間加入一個 uvm_analysis_fifo。FIFO 的本質是一塊快取加兩個 IMP。在 monitor 與 FIFO 的連結關係中，monitor 中依然是 analysis_port，FIFO 中是 uvm_analysis_imp，資料流和控制流的方向相同。在 scoreboard 與 FIFO 的連接關係中，scoreboard 中使用 blocking_get_port 埠：
```
class my_scoreboard extends uvm_scoreboard;
  my_transaction expect_queue[$];                      // 裝 expect value 的 queue
  uvm_blocking_get_port #(my_transaction) exp_port;    // 改成 port 主動取資料
  uvm_blocking_get_port #(my_transaction) act_port;
  …
endclass
…
task my_scoreboard::main_phase(uvm_phase phase);
  …
  fork
    while (1) begin
      exp_port.get(get_expect);            // Scoreboard 主動去 get tr
      expect_queue.push_back(get_expect);
    end
    while (1) begin
      act_port.get(get_actual);            // actual data 不用放到 queue 因為直接拿 expect value 去比對
      …
    end
  join
endtask
```
而 FIFO 中使用的是一個 get 埠的 IMP。在這種連接關係中，控制流是從 scoreboard 到 FIFO，而資料流是從 FIFO 到 scoreboard。
<img width="1064" height="788" alt="image" src="https://github.com/user-attachments/assets/062735af-73f4-4b7b-97c0-eb9da1e73295" />
env code
```
class my_env extends uvm_env;

  my_agent i_agt;
  my_agent o_agt;
  my_model mdl;
  my_scoreboard scb;

  uvm_tlm_analysis_fifo #(my_transaction) agt_scb_fifo;
  uvm_tlm_analysis_fifo #(my_transaction) agt_mdl_fifo;
  uvm_tlm_analysis_fifo #(my_transaction) mdl_scb_fifo;
  …
endclass

function void my_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  i_agt.ap.connect(agt_mdl_fifo.analysis_export);
  mdl.port.connect(agt_mdl_fifo.blocking_get_export);
  mdl.ap.connect(mdl_scb_fifo.analysis_export);
  scb.exp_port.connect(mdl_scb_fifo.blocking_get_export);
  o_agt.ap.connect(agt_scb_fifo.analysis_export);
  scb.act_port.connect(agt_scb_fifo.blocking_get_export);
endfunction
```
FIFO 中有兩個 IMP，但是在上面的連接關係中，FIFO 中卻是 EXPORT，這是為什麼呢？實際上，FIFO 中的 analysis_export 和 blocking_get_export 雖然名字中有關鍵字 export，但其型態卻是 IMP。UVM 為了掩飾 IMP 的存在，在它們的命名中加入了 export 關鍵字。如 analysis_export 的原型如下：
```
uvm_analysis_imp #(T, uvm_tlm_analysis_fifo #(T)) analysis_export;
```
* 第一個好處是不必在 scoreboard 中再寫一個名字為 write 的函數。 scoreboard 可以按照自己的步調工作，而不必跟著 monitor 的節奏
* 第二個好處是 FIFO 的存在隱藏了 IMP，這對初學者來說比較容易理解
* 第三個好處是可以輕易解決上一節講到的當 reference model 和 monitor 同時連接到 scoreboard 該如何處理的問題。事實上，FIFO 的存在自然而然地解決了它，這根本就不是一個問題了。
## FIFO 上的連接埠及調試
一個FIFO中有眾多的端口
<img width="1212" height="494" alt="image" src="https://github.com/user-attachments/assets/fa186f3b-f731-46ec-8819-6f725e08eccf" />
* **圓圈:** 表示的 EXPORT 雖然名字中有 export，但本質上都是 IMP。
  * 包含了 12 種 IMP，用於分別和相應的 PORT 及 EXPORT 連接
* **peek 系列端口**
  * peek 埠與 get 相似，其資料流、控制流都相似，唯一的差別在於當 get 任務被呼叫時，FIFO 內部快取會少一個 transaction，而 peek 被呼叫時，FIFO 會把 transaction 複製一份發送出去，其內部快取中的 transaction 數量並不會減少
* 還有兩個 analysis_port：put_ap 和 get_ap
  * 當 FIFO 上的 blocking_put_export 或 put_export 被連接到一個 blocking_put_port 或 put_port 上時，FIFO 內部被定義的 put 任務被調用，這個 put 任務把傳遞過來的 transaction 放在 FIFO 內部的緩存裡，同時，把這個 transaction 透過 put_ap 使用 write 函數送出去。 FIFO 的 put 任務定義如下：
```
virtual task put( input T t );
    m.put( t );          // m 即是 FIFO 內部的緩存，使用 SystemVerilog 中的 mailbox 來實現
    put_ap.write( t );
endtask
```
與 put_ap 相似，當 FIFO 的 get 任務被呼叫時，同樣會有一個 transaction 從 get_ap 上發出：
```
virtual task get( output T t );
    m_pending_blocked_gets++;
    m.get( t );
    m_pending_blocked_gets--;
    get_ap.write( t );
endtask
```
一個 blocking_get_port 連接到了 FIFO 上，當它呼叫 get 任務獲取 transaction 時就會呼叫 FIFO 的 get 任務。除此之外，FIFO 的 get_export、get_peek_export 和 blocking_get_peek_export 被對應的 PORT 或者 EXPORT 連線時，也會會呼叫 FIFO 的 get 任務
* FIFO 的類型有兩種，一種是上節介紹的 uvm_tlm_analysis_fifo，另外一種是 uvm_tlm_fifo
  * 這兩者的唯一差異在於前者有一個 analysis_export 端口，並且有一個 write 函數，而後者沒有
* FIFO 中的眾多連接埠方便了使用者的使用，同樣的，UVM 也提供了幾個函數用於 FIFO 的調試
  * **used 函數**用於查詢 FIFO 快取中有多少 transaction
  * **is_empty 函數**用來判斷目前 FIFO 快取是否為空
  * **is_full 函數**用於判斷當前 FIFO 快取是否已經滿了
  * **flush 函數**用於清空 FIFO 快取中的所有數據，它一般用於重設等操作
  * **size 函數**可以返回 FIFO 上限值
  * 作為一個快取來說，其能儲存的 transaction 是有限的。最大值是定義在 FIFO 的 new 函數，原型如下：
```
function new(string name, uvm_component parent = null, int size = 1);
```
FIFO 本質上是一個 component，所以其前兩個參數是 uvm_component 的 new 函式中的兩個參數。**第三個參數是 size，用於設定FIFO緩存的上限，在預設的情況下為1**。若要把快取設定為**無限大小，將傳入的 size 參數設為 0 即可**
## 用 FIFO 還是用 IMP
* 用 FIFO 通訊的方法中
  * 完全隱藏了 IMP。使用者可以完全不關心 IMP。尤其是當 scoreboard 面臨多個 IMP，需要為 IMP 聲明一個後綴時，這種優勢更加明顯
  * FIFO 連線的方式增加了 env 中程式碼的複雜度，滿滿的看起來似乎都是與 FIFO 相關的程式碼 (connect 的點變多)。尤其是當要連接的連接埠數量眾多時，這個缺點更加明顯
不過對於使用連接埠數組的情況，FIFO要優於IMP。假如參考模型中有16個類似連接埠要和scoreboard中對應的連接埠相互通信，如
此多數量的端口，在參考模型中可以使用端口數組來實現：
未完~~~~

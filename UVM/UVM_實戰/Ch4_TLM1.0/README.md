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
UVM 中使用 connect 函數來建立連線關係。如 A 要和 B 通訊（A 是發起者），那麼可以這麼寫：
A.port.connect（B.export），但是不能寫成 B.export.connect（A.port）。
只有發起者才能呼叫 connect 函數，而被動承擔者則作為 connect 的參數。
```
class A extends uvm_component;
  `uvm_component_utils(A)
  uvm_blocking_put_port#(my_transaction) A_port;
…
endclass

function void A::build_phase(uvm_phase phase);
  super.build_phase(phase);
  A_port = new("A_port", this);
endfunction

task A::main_phase(uvm_phase phase);
endtask
```

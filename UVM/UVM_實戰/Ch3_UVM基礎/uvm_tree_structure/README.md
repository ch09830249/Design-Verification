* 使用樹狀結構主要目的是，要讓 parent 能掌握它底下有哪些 children，同時 child 知道自己的 parent 是誰，parent 就不會用到一個根本不存在的 child
* 當 child 實例化的時候，指定一個 parent 的變量，同時在每一個 component 的內部維護一個數組 m_children，當 child 實例化時，就把 child 的指標加入 parent 的 m_children 陣列中。這樣才能讓 parent 知道 child 是自己的孩子，同時也才能讓 child 知道 parent 是自己的父母。
# uvm_component 中的 parent 參數
UVM 透過 uvm_component 來實現樹狀結構。所有的 UVM 樹的結點本質上都是一個 uvm_component。每個 uvm_component 都有一個特點：它們在 new 的時候，需要指定一個類型為 uvm_component、名字是 parent 的變數：
```
function new(string name, uvm_component parent);
```
# UVM 樹的根
UVM 是以樹的形式組織在一起的，作為一棵樹來說，其樹根在哪裡？其樹葉又是哪些呢？從第2章的例子來看，似乎樹根應該就是 uvm_test。在測試案例裡實例化 env，在 env 裡實例化 scoreboard、reference model、agent、在 agent 裡面實例化 sequencer、
driver 和 monitor。 scoreboard、reference model、sequencer、driver 和 monitor 都是樹的葉子，樹到此為止，沒有更多的葉子了。關於葉子的判斷是正確的，但是關於樹根的推論是錯誤的。
UVM 中真正的樹根是一個稱為 uvm_top 的東西
![image](https://github.com/user-attachments/assets/1de98988-7eee-4186-8e89-83247d2bdfdf)
# 層次結構相關函數
* **get_parent 函數**
  * 用於得到目前實例的parent
```
extern virtual function uvm_component get_parent ();
```
* **get_child 函數**
  * 與 get_parent 不同的是，get_child 需要一個 string 類型的參數 name，表示此 child 實例在實例化時指定的名字。因為一個component
只有一個 parent，所以 get_parent 不需要指定參數；而可能有多個 child，所以必須指定 name 參數。
```
extern function uvm_component get_child (string name);
```
* **get_children 函數**
  * 得到所有的child
```
extern function void get_children(ref uvm_component children[$]);
```
* **get_first_child 和 get_next_child 函數**
  * 除了一次得到所有的 child 外，還可以使用 get_first_child 和 get_next_child 的組合依序得到所有的 child
```
# extern function int get_first_child (ref string name);
# extern function int get_next_child (ref string name);

string name;
uvm_component child;
if (comp.get_first_child(name))
   do begin
      child = comp.get_child(name);
      child.print();
   end while (comp.get_next_child(name));
```
* **get_num_children 函數**
  * 用於傳回目前 component 所擁有的child的數量

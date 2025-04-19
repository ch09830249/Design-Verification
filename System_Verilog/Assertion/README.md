```
always_comb
begin
  a_ia: assert (a && b);
end
```
* 只有 a 或 b 發生變化時去 assertion 做檢查
![image](https://github.com/user-attachments/assets/89a300b5-9ef0-40c0-b323-c4c5401f115b)  
```
a_cc: assert property(@(posedge clk)
                                    not (a && b));
```
![image](https://github.com/user-attachments/assets/399a1456-b3b4-413d-80cc-966f780758ca)  
```
sequence s2;
  @(poseedge clk) $rose(a);  // 上一拍為低, 這拍為高
endsequence
```
![image](https://github.com/user-attachments/assets/098136e4-35ef-4686-80d0-3e1a4fc909fe)  
為甚麼不是 timestamp 1 的時候呢?  
因為 a 是因為 posedge 才驅動的, 所以一定會 posedge 之後 a 才拉起來, 所以在 timestamp 1 時 a 為 0  
```
sequence s3;
  @(poseedge clk) a || b;
endsequence
```
![image](https://github.com/user-attachments/assets/84a2b63c-6cb2-4f6f-b9d6-cf80065e5c04)  
這裡要看時鐘 posedge 左邊的值才採樣的值  
```
sequence s4;
  @(poseedge clk) a ##2 b;  // 當前採樣的 a 為高, 兩拍後 b 也採樣為高
endsequence
```
![image](https://github.com/user-attachments/assets/4b05dac5-66cc-45ee-b04c-cc4fda103690)  
```
sequence s6;
  @(poseedge clk) a ##2 b;  // 當前採樣的 a 為高, 兩拍後 b 也採樣為高
endsequence

property p6;
  not s6;
endproperty

a6: assert property(p6);
```
![image](https://github.com/user-attachments/assets/9931da76-b2c0-48d1-aa57-e4db8dcc0828)  
![image](https://github.com/user-attachments/assets/d2f65df9-2ad8-437f-ae2b-26df06cb3cd8)  
```
property p8;
  @(poseedge clk) a |-> b;  // 在先行條件滿足時 (a), 在同一拍看後續表達式是否也滿足 (b)
endproperty

a8: assert property(p8);
```
![image](https://github.com/user-attachments/assets/9ceb345b-990d-461b-aef6-8f0c8772d7af)  

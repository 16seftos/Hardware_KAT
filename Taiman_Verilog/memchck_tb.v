module memcheck_tb;
  
  reg clk;
  reg [31:0] addr;
  reg memwrite; 
  reg memread;
  wire rd;
  wire w;
  
  memcheck dut(
    .clk(clk),
    .addr(addr),
    .memwrite(memwrite),
    .memread(memread),
    .rd(rd),
    .w(w));
  
  initial begin
    //dump waves
    $dumpfile("dump.vcd");
    $dumpvars(1,memcheck_tb);
    clk = 0;
    
    #10 addr = 32'b00000000000000000000000000000001;
        memwrite = 1;
        memread = 0;
    
    #10 addr = 32'b00000000000000000000000000000010;
        memwrite = 0;
        memread = 1; 
    
    #10 addr = 32'b00000000000000000000000000001000;
        memwrite = 1;
        memread = 0;
    
    #10 $finish;
    
  end
  
  always #5 clk = ~clk;
  
endmodule
`timescale 1ns / 1ps

//Taint Testing verilog code

module taint(i, o);
  output [63:0] o;
  reg [63:0] o;
  input [63:0] i;

  reg [63:0] internal0;
  reg [63:0] internal1;
  reg [63:0] internal2;

  always @(*) begin
    internal2 = 0;
    internal1 = 0;
    internal0 = 0;
    o = 0;
    if (((((i >> 64) & (-1 >> 63)) == 1) | (((i >> 32) & (-1 >> 63)) == 1))) begin
      internal2 = (9223372035781033983 & i);
      //Check -<large number>?
      internal0 = (-9223372035781033984 | internal2);
    end else begin
    end
    if (~((((i >> 64) & (-1 >> 63)) == 1) | (((i >> 32) & (-1 >> 63)) == 1))) begin
      internal1 = i;
    end else begin 
    end
    o = (internal0 | internal1);
  end
endmodule
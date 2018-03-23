`timescale 1ns / 1ps

module secjmp(i, o);
  output [63:0] o;
  reg [63:0] o;
  input [63:0] i;
  reg [63:0] internal0;
  reg [63:0] internal1;

  always @(*) begin
    internal1 = 0;
    internal0 = 0;
    o = 0;
    if (((((i >> 26) & (-1 >> 58)) == 2) | (((i >> 26) & (-1 >> 58)) == 3))) begin
      if (~(((i >> 0) & (-1 >> 38)) == 0)) begin
        internal0 = i;
      end else begin
      end
    end else begin
    end
    if (~((((i >> 26) & (-1 >> 58)) == 2) | (((i >> 26) & (-1 >> 58)) == 3))) begin
      internal1 = i;
    end else begin
    end
    o = (internal0 | internal1);
  end
  
endmodule

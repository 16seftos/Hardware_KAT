`timescale 1ns / 1ps

//SFI Testing verilog code

module SFI(ri, ro);
  output [63:0] ro;
  reg [63:0] ro;
  input [63:0] ri;

  reg [63:0] internal0;
  reg [63:0] internal1;
  reg [63:0] internal2;

  always @(*)begin
    internal2 = 0;
    internal1 = 0;
    internal0 = 0;
    ro = 0;
    if (((((((((((((ri >> 26) & (-1 >> 58)) == 40) | (((ri >> 26) & (-1 >> 58)) == 56)) | (((ri >> 26) & (-1 >> 58)) == 60)) | (((ri >> 26) & (-1 >> 58)) == 63)) | (((ri >> 26) & (-1 >> 58)) == 44)) | (((ri >> 26) & (-1 >> 58)) == 45)) | (((ri >> 26) & (-1 >> 58)) == 41)) | (((ri >> 26) & (-1 >> 58)) == 43)) | (((ri >> 26) & (-1 >> 58)) == 42)) | (((ri >> 26) & (-1 >> 58)) == 46))) begin
      internal2 = (72057594037927935 & ri);
      internal0 = (-6701356245527298049 | internal2);
    end else begin
    end
    if (~((((((((((((ri >> 26) & (-1 >> 58)) == 40) | (((ri >> 26) & (-1 >> 58)) == 56)) | (((ri >> 26) & (-1 >> 58)) == 60)) | (((ri >> 26) & (-1 >> 58)) == 63)) | (((ri >> 26) & (-1 >> 58)) == 44)) | (((ri >> 26) & (-1 >> 58)) == 45)) | (((ri >> 26) & (-1 >> 58)) == 41)) | (((ri >> 26) & (-1 >> 58)) == 43)) | (((ri >> 26) & (-1 >> 58)) == 42)) | (((ri >> 26) & (-1 >> 58)) == 46))) begin
      internal1 = ri;
    end else begin
    end
    ro = (internal0 | internal1);
  end
endmodule
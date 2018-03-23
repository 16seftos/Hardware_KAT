module SCF(i, o);
output [63:0] o;
reg [63:0] o;
input [63:0] i;
reg [63:0] internal0;
reg [63:0] internal1;
reg [63:0] internal2;
reg [63:0] internal3;
reg [63:0] internal4;
reg [63:0] internal5;
reg [63:0] internal6;
reg [63:0] internal7;
always @(*)
begin
 internal7 = 0;
 internal6 = 0;
 internal5 = 0;
 internal4 = 0;
 internal3 = 0;
 internal2 = 0;
 internal1 = 0;
 internal0 = 0;
 o = 0;
if (((((((i >> 26) & (-1 >> 58)) == 4) | (((i >> 26) & (-1 >> 58)) == 7)) | (((i >> 26) & (-1 >> 58)) == 6)) | (((i >> 26) & (-1 >> 58)) == 5)))
begin
if (~(((i >> 32) & (-1 >> 32)) == 0))
begin
 internal0 = i;
end
else begin
end
end
else begin
end
if (~((((((i >> 26) & (-1 >> 58)) == 4) | (((i >> 26) & (-1 >> 58)) == 7)) | (((i >> 26) & (-1 >> 58)) == 6)) | (((i >> 26) & (-1 >> 58)) == 5)))
begin
if (((((i >> 26) & (-1 >> 58)) == 2) | (((i >> 26) & (-1 >> 58)) == 3)))
begin
if (~(((i >> 0) & (-1 >> 38)) == 0))
begin
 internal2 = i;
end
else begin
end
end
else begin
end
if (~((((i >> 26) & (-1 >> 58)) == 2) | (((i >> 26) & (-1 >> 58)) == 3)))
begin
if (((((i >> 26) & (-1 >> 58)) == 0) & ((((i >> 0) & (-1 >> 58)) == 9) | (((i >> 0) & (-1 >> 58)) == 8))))
begin
if (~(((i >> 32) & (-1 >> 32)) == 0))
begin
 internal4 = i;
end
else begin
end
end
else begin
end
if (~((((i >> 26) & (-1 >> 58)) == 0) & ((((i >> 0) & (-1 >> 58)) == 9) | (((i >> 0) & (-1 >> 58)) == 8))))
begin
if (((((i >> 26) & (-1 >> 58)) == 1) & ((((((i >> 16) & (-1 >> 59)) == 1) | (((i >> 16) & (-1 >> 59)) == 17)) | (((i >> 16) & (-1 >> 59)) == 0)) | (((i >> 16) & (-1 >> 59)) == 16))))
begin
if (~(((i >> 32) & (-1 >> 32)) == 0))
begin
 internal6 = i;
end
else begin
end
end
else begin
end
if (~((((i >> 26) & (-1 >> 58)) == 1) & ((((((i >> 16) & (-1 >> 59)) == 1) | (((i >> 16) & (-1 >> 59)) == 17)) | (((i >> 16) & (-1 >> 59)) == 0)) | (((i >> 16) & (-1 >> 59)) == 16))))
begin
 internal7 = i;
end
else begin
end
 internal5 = (internal6 | internal7);


end
else begin
end
 internal3 = (internal4 | internal5);


end
else begin
end
 internal1 = (internal2 | internal3);


end
else begin
end
 o = (internal0 | internal1);



end
endmodule


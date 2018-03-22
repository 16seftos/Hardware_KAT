`timescale 1ns / 1ps

////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer:
//
// Create Date:   18:22:49 03/16/2018
// Design Name:   SFI
// Module Name:   /home/seaghan/Desktop/SecKat/verilog_tests/SFI/xilinx/SFI/SFI_tb.v
// Project Name:  SFI
// Target Device:  
// Tool versions:  
// Description: 
//
// Verilog Test Fixture created by ISE for module: SFI
//
// Dependencies:
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
////////////////////////////////////////////////////////////////////////////////

module SFI_tb;

  // Inputs
  reg [63:0] ri;

  // Outputs
  wire [63:0] ro;

  // Instantiate the Unit Under Test (UUT)
  SFI uut (
    .ri(ri), 
    .ro(ro)
  );

  // Expected output register
  reg [63:0] exp_ro;
  reg all_pass;

  initial begin
    // Initialize Inputs
    ri = 0;
    exp_ro = 0;
    all_pass = 1;

    // Wait 10 ns for global reset to finish
    #10;
        
    // Add stimulus here
    $monitor("\nTesting");#1;
    $monitor("\nTestintg non-store instructions:");
      //these are from other programs I wrote, or random inputs
      ri     <= 64'hBAD0ADD012345678;
      exp_ro <= 64'hBAD0ADD012345678;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      ri     <= 64'h0021302000432820;
      exp_ro <= 64'h0021302000432820;
      // Should this pass the last 32b?
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      ri     <= 64'h2021000100031020;
      exp_ro <= 64'h2021000100031020;
      // Should this pass the last 32b?
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      ri     <= 64'h0123456789ABCDEF;
      exp_ro <= 64'h0123456789ABCDEF;
      // Should this pass the last 32b?
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
    #10;
    
    //GOOD TESTS
    $monitor("\nTestintg good eff addrs:");
      //SB
      ri     <= 64'hFAFA0000A0111111;
      exp_ro <= 64'hA2FA0000A0111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SC
      ri     <= 64'hFACA0001E0111111;
      exp_ro <= 64'hA2CA0001E0111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SCD
      ri     <= 64'h01000002F0111111;
      exp_ro <= 64'hA2000002F0111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SD
      ri     <= 64'h2A321403FC111111;
      exp_ro <= 64'hA2321403FC111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SDL
      ri     <= 64'hA1222004B8111111;
      exp_ro <= 64'hA2222004B8111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SDR
      ri     <= 64'hB1000005B4111111;
      exp_ro <= 64'hA2000005B4111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SH
      ri     <= 64'hF2CAFE06A4111111;
      exp_ro <= 64'hA2CAFE06A4111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SW
      ri     <= 64'hFFCAD007AC111111;
      exp_ro <= 64'hA2CAD007AC111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SWL
      ri     <= 64'h00000008A8111111;
      exp_ro <= 64'hA2000008A8111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SWR
      ri     <= 64'h44FACE09B8111111;
      exp_ro <= 64'hA2FACE09B8111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
    #10;
    
    //Bad Tests:
    $monitor("\nTestintg bad eff addrs:");
      //SB
      ri     <= 64'hA2000000A0111111;
      exp_ro <= 64'hA2000000A0111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SC
      ri     <= 64'hA20A0001E0111111;
      exp_ro <= 64'hA20A0001E0111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SCD
      ri     <= 64'hA2000002F0111111;
      exp_ro <= 64'hA2000002F0111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SD
      ri     <= 64'hA2321403FC111111;
      exp_ro <= 64'hA2321403FC111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SDL
      ri     <= 64'hA2222004B8111111;
      exp_ro <= 64'hA2222004B8111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SDR
      ri     <= 64'hA2000005B4111111;
      exp_ro <= 64'hA2000005B4111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SH
      ri     <= 64'hA2CAFE06A4111111;
      exp_ro <= 64'hA2CAFE06A4111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SW
      ri     <= 64'hA2CAD007AC111111;
      exp_ro <= 64'hA2CAD007AC111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SWL
      ri     <= 64'hA2000008A8111111;
      exp_ro <= 64'hA2000008A8111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
      //SWR
      ri     <= 64'hA2FACE09B8111111;
      exp_ro <= 64'hA2FACE09B8111111;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
        all_pass = 0;
      end
    #10;
    #10;
    
    
    //FINISHED TESTING
    $monitor("\nDone testing, exiting\n");#1;
    if(all_pass == 1) begin
      $monitor("All Pass");#1;
    end else begin
      $monitor("Not all pass");#1;
    end
    $finish();
      
  end
      
endmodule


<?php

// ini_set('display_errors', 'On');
// error_reporting(E_ALL | E_STRICT);

function execCommand($tsrc, $hsenvdir, $log) {
  $packagedir  = $hsenvdir . '/lib/ghc-7.6.3/package.conf.d';
  $bindir      = $hsenvdir . '/cabal/bin';
  $cmd_lang    = 'LANG=en_US.UTF-8'; 
  $cmd_path    = 'PATH=' . $bindir . ':$PATH';
  $cmd_packdir = 'GHC_PACKAGE_PATH='.$packagedir.':' ;
  $cmd_checker = 'nanojs liquid '.$tsrc ;
  $cmd         = $cmd_lang.' '.$cmd_path.' '.$cmd_packdir.' '.$cmd_checker.' > '.$log.' 2>&1';
  return $cmd;
}

function writeFileRaw($fname, $rawstring){
  $f = fopen($fname, "w");
  fwrite($f, $rawstring);
  fclose($f);
}

function getCrash($logfile){ 
  $wflag = 0;
  $crash = "";
  $fh    = fopen($logfile, 'r');

  while (!feof($fh)){
    $s = fgets($fh);
    if (strpos($s, "*** ERROR ***") !== false){
      $wflag    = $wflag + 1;
    } 
    if ($wflag == 3){
      $crash = $crash . $s;
    }
  } 
  fclose($fh);
  return $crash;
}

/*
function getResultAndWarns($outfile){
  $wflag = 0;
  $warns = array();
  $res   = "";

  $failflag = 1;

  if (file_exists($outfile)){
    $fh = fopen($outfile, 'r');
    while (!feof($fh)){
      $s = fgets($fh);
      if ($wflag == 1){           // Skip the first "Unsafe" start chewing remainder of lines
        $warns[] = substr($s, 8); // Eschew the prefix "WARNING:" 
      }
      if (strpos($s,"Safe") !== false){
        $failflag = 0; 
        $wflag    = 0;
      }
      if (strpos($s,"Unsafe") !== false){
        $failflag = 0; 
        $wflag    = 1;
      }
    } 
    fclose($fh);
  } 

  if ($failflag == 1){
    $res = "crash";
  } else if ($wflag == 0){
    $res = "safe";
  } else {
    $res = "unsafe";
  }

  return array( "result" => $res
              , "warns"  => $warns ); 

}

*/
////////////////////////////////////////////////////////////////////////////////////
//////////////////// Top Level Server //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////


// Get inputs
$data             = file_get_contents("php://input");
$query            = json_decode($data);
// $packagedir       = "/home/rjhala/.ghc/x86_64-linux-7.4.1/package.conf.d/";
$hsenvdir         = "/home/rjhala/research/liquid/.hsenv_liquid/";
$log              = "log";


// echo 'HELLO TO HELL!\n';
// echo ('PGM\n' . $query->program) ;
// echo ('QUALS\n' . $query->qualifiers);

// Generate temporary filenames 
$t                = time();
$tsrc             = $t    . ".js";
$thq              = $tsrc . ".hquals";
$thtml            = $tsrc . ".html"; 
$tout             = $tsrc . ".out";  
$terr             = $tsrc . ".err";
$tjson            = $tsrc . ".json";

// Write query to files
writeFileRaw($thq, $query->qualifiers);
writeFileRaw($tsrc, $query->program);

// echo 'wrote files';

// Run solver
$cmd              = execCommand($tsrc, $hsenvdir, $log);
writeFileRaw("cmdlog", $cmd);
$res              = shell_exec($cmd);

// Parse results
// $out              = getResultAndWarns($tout) ;
$out              = array();
$out['crash']     = getCrash($log)           ;       
$out['annotHtml'] = file_get_contents($thtml);
$out['annots']    = json_decode(file_get_contents($tjson));

// echo 'result = ' . $out['result'];
// echo 'warns = '  . $out['warns'];

// Cleanup temporary files
// shell_exec("rm -rf ".$tsrc."hi");
// shell_exec("rm -rf ".$tsrc."o");
shell_exec("mv ".$t."* saved/");

// Put outputs 
echo json_encode($out);


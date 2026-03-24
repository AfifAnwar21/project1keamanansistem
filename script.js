(function(global){

function strToBytes(str) {
  var out = [];
  for(var i=0; i<str.length; ++i) out.push(str.charCodeAt(i) & 0xff);
  return out;
}
function bytesToStr(bytes) {
  return String.fromCharCode.apply(null, bytes);
}

function bytesToBase64(arr){
  if(typeof btoa!=="undefined") return btoa(String.fromCharCode.apply(null,arr));
  return Buffer.from(arr).toString('base64');
}
function base64ToBytes(base64){
  if(typeof atob!=="undefined"){
    var bin = atob(base64);
    var out = [];
    for(var i=0;i<bin.length;++i) out.push(bin.charCodeAt(i));
    return out;
  }
  // Node.js
  return Array.from(Buffer.from(base64, 'base64'));
}

function padPKCS7(data, blocklen) {
  var padlen = blocklen - (data.length % blocklen);
  if(padlen===0) padlen = blocklen;
  var res = data.slice();
  for(var i=0;i<padlen;++i) res.push(padlen);
  return res;
}
function unpadPKCS7(data) {
  if(!data.length) return data;
  var pad = data[data.length-1];
  if(pad<1 || pad>16) return data;
  // Validate pad
  for(var i=data.length-pad;i<data.length;i++) if(data[i]!==pad) return data;
  return data.slice(0,data.length-pad);
}

function xorBlocks(a,b){ // mutates a
  for(var i=0;i<a.length;i++) a[i] ^= b[i];
  return a;
}
function clone(a){return a.slice();}

// --- [ AES core: S-Box etc. ] ---
var SBOX = [
99,124,119,123,242,107,111,197,48,1,103,43,254,215,171,118,
202,130,201,125,250,89,71,240,173,212,162,175,156,164,114,192,
183,253,147,38,54,63,247,204,52,165,229,241,113,216,49,21,
4,199,35,195,24,150,5,154,7,18,128,226,235,39,178,117,
9,131,44,26,27,110,90,160,82,59,214,179,41,227,47,132,
83,209,0,237,32,252,177,91,106,203,190,57,74,76,88,207,
208,239,170,251,67,77,51,133,69,249,2,127,80,60,159,168,
81,163,64,143,146,157,56,245,188,182,218,33,16,255,243,210,
205,12,19,236,95,151,68,23,196,167,126,61,100,93,25,115,
96,129,79,220,34,42,144,136,70,238,184,20,222,94,11,219,
224,50,58,10,73,6,36,92,194,211,172,98,145,149,228,121,
231,200,55,109,141,213,78,169,108,86,244,234,101,122,174,8,
186,120,37,46,28,166,180,198,232,221,116,31,75,189,139,138,
112,62,181,102,72,3,246,14,97,53,87,185,134,193,29,158,
225,248,152,17,105,217,142,148,155,30,135,233,206,85,40,223,
140,161,137,13,191,230,66,104,65,153,45,15,176,84,187,22
];
var INV_SBOX = [
82,9,106,213,48,54,165,56,191,64,163,158,129,243,215,251,
124,227,57,130,155,47,255,135,52,142,67,68,196,222,233,203,
84,123,148,50,166,194,35,61,238,76,149,11,66,250,195,78,
8,46,161,102,40,217,36,178,118,91,162,73,109,139,209,37,
114,248,246,100,134,104,152,22,212,164,92,204,93,101,182,146,
108,112,72,80,253,237,185,218,94,21,70,87,167,141,157,132,
144,216,171,0,140,188,211,10,247,228,88,5,184,179,69,6,
208,44,30,143,202,63,15,2,193,175,189,3,1,19,138,107,
58,145,17,65,79,103,220,234,151,242,207,206,240,180,230,115,
150,172,116,34,231,173,53,133,226,249,55,232,28,117,223,110,
71,241,26,113,29,41,197,137,111,183,98,14,170,24,190,27,
252,86,62,75,198,210,121,32,154,219,192,254,120,205,90,244,
31,221,168,51,136,7,199,49,177,18,16,89,39,128,236,95,
96,81,127,169,25,181,74,13,45,229,122,159,147,201,156,239,
160,224,59,77,174,42,245,176,200,235,187,60,131,83,153,97,
23,43,4,126,186,119,214,38,225,105,20,99,85,33,12,125
];
var RCON = [
0x00,0x01,0x02,0x04,0x08,0x10,0x20,0x40,0x80,0x1b,0x36
];

// Galois multiplication
function xtime(a) { return ((a<<1)^( ((a>>7)&1)*0x1b ))&0xff; }
function mul(a,b){
  var t = 0;
  for(var i=0;i<8;i++){
    if(b&1) t^=a;
    var hbs = a & 0x80;
    a = (a<<1)&0xff;
    if(hbs) a^=0x1b;
    b>>=1;
  }
  return t;
}

// Key expansion: input 16 (128-bit) bytes, output 176 bytes (11 x 16 bytes)
function expandKey(keyBytes) {
  var w = [];
  for(var i=0;i<16;i++) w[i]=keyBytes[i];
  for(var i=16;i<176;i++){
    var temp = w.slice(i-4,i);
    if(i%16===0){
      // rot+sub+Rcon
      temp.push(temp.shift());
      for(var j=0;j<4;j++) temp[j]=SBOX[temp[j]];
      temp[0]^=RCON[i/16];
    }
    w[i]=w[i-16]^temp[0];
    w[i+1]=w[i-15]^temp[1];
    w[i+2]=w[i-14]^temp[2];
    w[i+3]=w[i-13]^temp[3];
    i+=3;
  }
  return w;
}

// AddRoundKey
function addRoundKey(s, w, off){
  for(var i=0;i<16;i++) s[i]^=w[off+i];
}

// SubBytes
function subBytes(s){
  for(var i=0;i<16;i++) s[i]=SBOX[s[i]];
}
function invSubBytes(s){
  for(var i=0;i<16;i++) s[i]=INV_SBOX[s[i]];
}

// ShiftRows
function shiftRows(s){
  var t=clone(s);
  s[0]=t[0]; s[1]=t[5]; s[2]=t[10]; s[3]=t[15];
  s[4]=t[4]; s[5]=t[9]; s[6]=t[14]; s[7]=t[3];
  s[8]=t[8]; s[9]=t[13]; s[10]=t[2]; s[11]=t[7];
  s[12]=t[12];s[13]=t[1]; s[14]=t[6]; s[15]=t[11];
}
function invShiftRows(s){
  var t=clone(s);
  s[0]=t[0]; s[1]=t[13]; s[2]=t[10]; s[3]=t[7];
  s[4]=t[4]; s[5]=t[1]; s[6]=t[14]; s[7]=t[11];
  s[8]=t[8]; s[9]=t[5]; s[10]=t[2]; s[11]=t[15];
  s[12]=t[12];s[13]=t[9]; s[14]=t[6]; s[15]=t[3];
}

// MixColumns
function mixColumns(s){
  for(var i=0;i<4;i++){
    var a = s.slice(i*4, i*4+4);
    s[i*4+0] = mul(a[0],2)^mul(a[1],3)^a[2]^a[3];
    s[i*4+1] = a[0]^mul(a[1],2)^mul(a[2],3)^a[3];
    s[i*4+2] = a[0]^a[1]^mul(a[2],2)^mul(a[3],3);
    s[i*4+3] = mul(a[0],3)^a[1]^a[2]^mul(a[3],2);
  }
}
function invMixColumns(s){
  for(var i=0;i<4;i++){
    var a = s.slice(i*4, i*4+4);
    s[i*4+0]=mul(a[0],0x0e)^mul(a[1],0x0b)^mul(a[2],0x0d)^mul(a[3],0x09);
    s[i*4+1]=mul(a[0],0x09)^mul(a[1],0x0e)^mul(a[2],0x0b)^mul(a[3],0x0d);
    s[i*4+2]=mul(a[0],0x0d)^mul(a[1],0x09)^mul(a[2],0x0e)^mul(a[3],0x0b);
    s[i*4+3]=mul(a[0],0x0b)^a[1]^a[2]^mul(a[3],0x0e);
  }
}

// AES Block Encrypt/Decrypt (128-bit block, 128-bit key)
function aesBlockEncrypt(block, w) {
  var state = block.slice();
  addRoundKey(state, w, 0);
  for(var r=1;r<=9;r++){
    subBytes(state);
    shiftRows(state);
    mixColumns(state);
    addRoundKey(state, w, r*16);
  }
  subBytes(state);
  shiftRows(state);
  addRoundKey(state, w, 160);
  return state;
}
function aesBlockDecrypt(block, w) {
  var state = block.slice();
  addRoundKey(state,w,160);
  for(var r=9;r>=1;r--){
    invShiftRows(state);
    invSubBytes(state);
    addRoundKey(state, w, r*16);
    invMixColumns(state);
  }
  invShiftRows(state);
  invSubBytes(state);
  addRoundKey(state,w,0);
  return state;
}

// -- [ Mode Handling ] --
// mode: ECB, CBC, CFB, OFB

function normalizeKey(key){
  var k = strToBytes(key||"");
  if(k.length<16) for(var i=k.length;i<16;i++) k.push(0);
  else if(k.length>16) k=k.slice(0,16);
  return k;
}
function normalizeIV(iv){
  if(!iv) iv = "1234567890123456";
  var v = strToBytes(iv);
  if(v.length<16) for(var i=v.length;i<16;i++) v.push(0);
  else if(v.length>16) v=v.slice(0,16);
  return v;
}

// Implementasi Encrypt dan Decrypt untuk mode CFB dan OFB

function encryptCFB(plaintext, key, iv) {
  var ptBytes = strToBytes(plaintext);
  var w = expandKey(key);
  var block = iv.slice();
  var i=0;
  var out = [];
  while(i<ptBytes.length){
    var stream = aesBlockEncrypt(block, w);
    var blen = Math.min(16, ptBytes.length-i);
    var buf = [];
    for(var j=0;j<blen;j++){
      buf.push(ptBytes[i+j]^stream[j]);
    }
    out = out.concat(buf);
    block = buf.slice(); // CFB: feedback dari ciphertext
    i += blen;
  }
  return out;
}
function decryptCFB(cipherBytes, key, iv) {
  var w = expandKey(key);
  var block = iv.slice();
  var i=0;
  var out = [];
  while(i<cipherBytes.length){
    var stream = aesBlockEncrypt(block, w);
    var blen = Math.min(16, cipherBytes.length-i);
    var buf = [];
    for(var j=0;j<blen;j++){
      buf.push(cipherBytes[i+j]^stream[j]);
    }
    out = out.concat(buf);
    block = cipherBytes.slice(i,i+blen); // CFB: feedback dari ciphertext
    i+=blen;
  }
  return out;
}

function encryptOFB(plaintext, key, iv) {
  var ptBytes = strToBytes(plaintext);
  var w = expandKey(key);
  var block = iv.slice();
  var i=0;
  var out = [];
  while(i<ptBytes.length){
    var stream = aesBlockEncrypt(block, w);
    var blen = Math.min(16, ptBytes.length-i);
    var buf = [];
    for(var j=0;j<blen;j++){
      buf.push(ptBytes[i+j]^stream[j]);
    }
    out = out.concat(buf);
    block = stream; // OFB: feedback dari stream
    i += blen;
  }
  return out;
}
function decryptOFB(cipherBytes, key, iv) {
  // Decrypt OFB is identical to encrypt
  var w = expandKey(key);
  var block = iv.slice();
  var i=0;
  var out = [];
  while(i<cipherBytes.length){
    var stream = aesBlockEncrypt(block, w);
    var blen = Math.min(16, cipherBytes.length-i);
    var buf = [];
    for(var j=0;j<blen;j++){
      buf.push(cipherBytes[i+j]^stream[j]);
    }
    out = out.concat(buf);
    block = stream;
    i+=blen;
  }
  return out;
}

function encryptAES(plaintext, key, opts){
  opts = opts||{};
  var mode = (opts.mode||"ECB").toUpperCase();
  if(["ECB","CBC","CFB","OFB"].indexOf(mode)===-1) throw new Error("Mode tidak dikenali");
  key = normalizeKey(key);
  var iv = (mode==="ECB") ? null : normalizeIV(opts.iv);

  var ptBytes = strToBytes(plaintext);
  var w = expandKey(key);

  var blocks = [];
  if(mode==="CFB"){
    blocks = encryptCFB(plaintext, key, iv);
  }else if(mode==="OFB"){
    blocks = encryptOFB(plaintext, key, iv);
  }else if(mode==="ECB"||mode==="CBC"){
    ptBytes = padPKCS7(ptBytes, 16);
    var prev = (mode==="CBC") ? iv.slice() : null;
    for(var i=0; i<ptBytes.length; i+=16){
      var chunk = ptBytes.slice(i,i+16);
      if(mode==="CBC") xorBlocks(chunk, prev);
      var enc = aesBlockEncrypt(chunk, w);
      if(mode==="CBC") prev = enc.slice();
      blocks = blocks.concat(enc);
    }
  }
  return bytesToBase64(blocks);
}

function decryptAES(cipherBase64, key, opts){
  opts = opts||{};
  var mode = (opts.mode||"ECB").toUpperCase();
  if(["ECB","CBC","CFB","OFB"].indexOf(mode)===-1) throw new Error("Mode tidak dikenali");
  key = normalizeKey(key);
  var iv = (mode==="ECB") ? null : normalizeIV(opts.iv);

  var ctBytes = base64ToBytes(cipherBase64);
  var w = expandKey(key);

  var blocks=[];
  if(mode==="CFB"){
    blocks = decryptCFB(ctBytes, key, iv);
  }else if(mode==="OFB"){
    blocks = decryptOFB(ctBytes, key, iv);
  }else if(mode==="ECB"||mode==="CBC"){
    var prev = (mode==="CBC") ? iv.slice() : null;
    for(var i=0;i<ctBytes.length;i+=16){
      var chunk = ctBytes.slice(i,i+16);
      var dec = aesBlockDecrypt(chunk, w);
      if(mode==="CBC") xorBlocks(dec, prev);
      if(mode==="CBC") prev = chunk.slice();
      blocks = blocks.concat(dec);
    }
    blocks = unpadPKCS7(blocks);
  }
  return bytesToStr(blocks);
}

// --- [ FIXED: Expose as AESLite global ] ---
// Mendaftarkan namespace global.AESLite agar API bisa diakses sebagai AESLite.encrypt / AESLite.decrypt

global.AESLite = {
  encrypt: encryptAES,
  decrypt: decryptAES,
  // Juga expose: untuk extensibility/support
  encryptAES: encryptAES,
  decryptAES: decryptAES
};

})(typeof window!=="undefined"?window:global);
#!/usr/bin/env python3
"""Split the compiled main.tex into L4DC main/supplement PDFs and check length.

Requires pypdf. All manuscript text stays in main.tex. Page numbers are retained
across the pair, and cross-part links open the accompanying PDF by name.
"""
from pathlib import Path
import hashlib,json,re,logging
from pypdf import PdfReader,PdfWriter
from pypdf.generic import DictionaryObject,NameObject,TextStringObject,BooleanObject,ArrayObject
HERE=Path(__file__).resolve().parent
OUT=HERE/'output/pdf'

class ManualAnnotationCopyWarning(logging.Filter):
 def filter(self,record):
  return not record.getMessage().startswith('Annotation sizes differ:')


def main():
 source=OUT/'paper_complete.pdf';reader=PdfReader(source);texts=[p.extract_text() or '' for p in reader.pages]
 refs=next(i for i,t in enumerate(texts) if re.search(r'^References\s*$',t,re.M))
 appendix=next(i for i,t in enumerate(texts) if 'Appendix A.' in t[:260])
 assert 0<refs<appendix<len(texts)
 destinations={n:reader.get_destination_page_number(d) for n,d in reader.named_destinations.items()}
 tex=(HERE/'main.tex').read_text();title=re.search(r'\\title(?:\[[^]]*\])?\{([^}]+)\}',tex)[1]
 authors=', '.join(re.findall(r'\\Name\{([^}]+)\}',tex.split('\\begin{document}',1)[0]))
 files=[('paper_main.pdf',range(appendix),'Main paper and references'),('paper_supplement.pdf',range(appendix,len(texts)),'Supplementary proofs and verification')]
 results=[]
 for index,(name,pages,subject) in enumerate(files):
  indices=set(pages);writer=PdfWriter();remote=files[1-index][0];changed=0
  positions={old:new for new,old in enumerate(pages)}
  # All annotations are reconstructed and counted below, so suppress only the
  # expected warning from deliberately excluding automatic annotation cloning.
  log=logging.getLogger('pypdf.generic._link');warning_filter=ManualAnnotationCopyWarning();log.addFilter(warning_filter)
  try:
   for original in pages:writer.add_page(reader.pages[original],excluded_keys=['/Annots'])
  finally:log.removeFilter(warning_filter)
  for destination_name,destination in reader.named_destinations.items():
   original=destinations[destination_name]
   if original in indices:
    array=ArrayObject([writer.pages[positions[original]].indirect_reference]+list(destination.dest_array[1:]))
    writer.add_named_destination_array(TextStringObject(destination_name),array)
  original_annotation_count=0
  for original in pages:
   for reference in reader.pages[original].get('/Annots',[]):
    annotation=reference.get_object().clone(writer,ignore_fields=['/P']);original_annotation_count+=1
    action=annotation.get('/A');action=action.get_object() if action else None
    if action and action.get('/S')=='/GoTo':
     destination=action.get('/D')
     assert isinstance(destination,str),destination
     assert destination in destinations,destination
     if destinations[destination] not in indices:
      annotation[NameObject('/A')]=DictionaryObject({NameObject('/S'):NameObject('/GoToR'),NameObject('/F'):TextStringObject(remote),NameObject('/D'):TextStringObject(destination),NameObject('/NewWindow'):BooleanObject(True)});changed+=1
    writer.add_annotation(positions[original],annotation)
  assert sum(len(p.get('/Annots',[])) for p in writer.pages)==original_annotation_count
  writer.add_metadata({'/Title':title+(' — Supplementary Material' if index else ''),'/Author':authors,'/Subject':subject,'/Creator':'L4DC submission export from main.tex'})
  with (OUT/name).open('wb') as stream:writer.write(stream)
  results.append({'file':name,'pages':len(pages),'original_pages':[min(indices)+1,max(indices)+1],'cross_part_links':changed,'annotations_preserved':original_annotation_count,'sha256':hashlib.sha256((OUT/name).read_bytes()).hexdigest()})
 exported=[PdfReader(OUT/x[0]) for x in files]
 for i,r in enumerate(exported):
  assert [p.extract_text() for p in r.pages]==[texts[j] for j in files[i][1]]
  for page in r.pages:
   for reference in page.get('/Annots',[]):
    a=reference.get_object().get('/A');a=a.get_object() if a else {}
    if a.get('/S')=='/GoTo':assert a['/D'] in r.named_destinations,a
    if a.get('/S')=='/GoToR':assert a['/D'] in exported[1-i].named_destinations,a
 record={'source':'main.tex','source_sha256':hashlib.sha256((HERE/'main.tex').read_bytes()).hexdigest(),'complete_pdf_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'main_text_pages':refs,'reference_pages':appendix-refs,'supplement_pages':len(texts)-appendix,'page_limit':10,'page_limit_satisfied':refs<=10,'pages_over_limit':max(0,refs-10),'cross_part_destinations_verified':True,'outputs':results}
 (OUT/'submission_manifest.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n')
 print('Main text: '+str(refs)+' pages; '+('within' if refs<=10 else 'OVER')+' the 10-page limit.')
 print('Main PDF: '+str(appendix)+' pages including references. Supplement: '+str(len(texts)-appendix)+' pages.')
 print('All cross-part PDF destinations verified.')
if __name__=='__main__':main()

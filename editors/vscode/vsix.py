"""Packs this directory into hailperin-VERSION.vsix, as vsce would, without Node.

A .vsix is a zip: the extension under `extension/`, a manifest, and the content types."""

import json
import zipfile
from pathlib import Path

here = Path(__file__).parent
meta = json.loads((here / "package.json").read_text())
files = ["package.json", "extension.js", "language-configuration.json", "syntaxes/hailperin.tmLanguage.json"]
license = here / "../../LICENSE"

manifest = f"""<?xml version="1.0" encoding="utf-8"?>
<PackageManifest Version="2.0.0" xmlns="http://schemas.microsoft.com/developer/vsx-schema/2011">
  <Metadata>
    <Identity Language="en-US" Id="{meta['name']}" Version="{meta['version']}" Publisher="{meta['publisher']}"/>
    <DisplayName>{meta['displayName']}</DisplayName>
    <Description xml:space="preserve">{meta['description']}</Description>
    <Categories>{','.join(meta['categories'])}</Categories>
    <Properties>
      <Property Id="Microsoft.VisualStudio.Code.Engine" Value="{meta['engines']['vscode']}"/>
    </Properties>
  </Metadata>
  <Installation>
    <InstallationTarget Id="Microsoft.VisualStudio.Code"/>
  </Installation>
  <Dependencies/>
  <Assets>
    <Asset Type="Microsoft.VisualStudio.Code.Manifest" Path="extension/package.json" Addressable="true"/>
  </Assets>
</PackageManifest>
"""

types = """<?xml version="1.0" encoding="utf-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
  <Default Extension=".json" ContentType="application/json"/>
  <Default Extension=".js" ContentType="application/javascript"/>
  <Default Extension=".vsixmanifest" ContentType="text/xml"/>
  <Default Extension=".txt" ContentType="text/plain"/>
</Types>
"""

out = here / f"hailperin-{meta['version']}.vsix"
with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as z:
    z.writestr("[Content_Types].xml", types)
    z.writestr("extension.vsixmanifest", manifest)
    for f in files:
        z.write(here / f, f"extension/{f}")
    if license.exists():
        z.write(license, "extension/LICENSE.txt")
print(out.name)
